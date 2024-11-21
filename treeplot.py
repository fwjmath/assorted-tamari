# -*- coding: utf-8 -*-

r"""
Plotting arbitrary labeled trees

This class implement a relatively simple algorithm to plot trees in a layered
fashion. The main idea is to keep track of the left and right limits of already
plotted sub-trees, then combine them together while minimizing the size gap
"""

# ****************************************************************************
#       Copyright (C) 2024 Wenjie Fang <fwjmath@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# ****************************************************************************

from sage.combinat.ordered_tree import LabelledOrderedTree, OrderedTree
from sage.plot.graphics import Graphics
from sage.plot.line import line
from sage.plot.polygon import polygon2d
from sage.plot.circle import circle
from sage.plot.text import text

class TreePlot:

    @staticmethod
    def __profile_distance(prof1, prof2, horiz):
        r"""
        Internal function, computes the distance between the roots of two
        adjacent subtrees.

        INPUT:
        - ``prof1``: the right profile of the first subtree
        - ``prof2``: the left profile of the second subtree

        OUTPUT:
        The distance between the two subtrees that is the smallest while keeping
        both subtrees at distance ``HORIZ``
        """
        # compute the common levels
        l = min(len(prof1), len(prof2))
        # compute the largest deviation among common levels
        dist = max([prof1[i] - prof2[i] for i in range(l)])
        # result: largest deviation plus horiz
        return dist + horiz
    
    
    @staticmethod
    def __compute_tree_profile(t: LabelledOrderedTree, horiz: float):
        r"""
        Internal function, computes the relative position of children for each
        node and the profile of the whole tree from both sides.

        The function returns:
        - a tuple of
          - a tuple of the original label and the list of relative positions
            of children
          - a list of recursively computed results for sub-trees.
        - a list of minimal positions for each level
        - a list of maximal positions for each level
        """
        def fusion_prof(prof, newprof, shift, isright=True): 
            # fusion two profiles
            size = max(len(prof), len(newprof))
            commsize = min(len(prof), len(newprof))
            choice = max if isright else min
            shift = shift if isright else -shift
            l = [choice(prof[i], newprof[i] + shift) for i in range(commsize)]
            if len(prof) >= len(newprof):
                l.extend(prof[commsize:])
            else:
                l.extend([x + shift for x in newprof[commsize:]])
            return l
            
        # Case of leaf
        if not t:
            return ((t.label(), []), []), [0], [0]
        # General case
        # First, get all the info from subtrees
        stlist, lprof, rprof = [], [], []
        for st in t:
            newst, stlprof, strprof = TreePlot.__compute_tree_profile(st, horiz)
            stlist.append(newst)
            lprof.append(stlprof)
            rprof.append(strprof)

        # Then compute the distances and positions
        # first, left-aligned positions
        k = len(stlist)
        lpos = [0]
        curprof = rprof[0]
        for i in range(k - 1):
            hdist = TreePlot.__profile_distance(curprof, lprof[i + 1], horiz)
            curprof = fusion_prof(curprof, rprof[i + 1], hdist)
            lpos.append(hdist)
        # then right-aligned positions, except when there are 1 or 2 subtrees
        if k <= 2:
            rpos = lpos
        else:
            rpos = [0]
            curprof = lprof[-1]
            for i in range(k - 1, -1, -1):
                hdist = TreePlot.__profile_distance(rprof[i], curprof, horiz)
                curprof = fusion_prof(curprof, lprof[i], hdist, isright=False)
                rpos.append(hdist)
            rpos.reverse()
            rpos = [rpos[0] - e for e in rpos]
        # then take the mean
        pos = [(lpos[i] + rpos[i]) / 2 for i in range(k)]

        # Now center the root in the middle of the whole tree
        # but not outside the interval of children
        subminpos = min([min(lprof[i]) + pos[i] for i in range(k)])
        submaxpos = max([max(rprof[i]) + pos[i] for i in range(k)])
        rootpos = (subminpos + submaxpos) / 2
        rootpos = min(max(0, rootpos), pos[-1])
        pos = [x - rootpos for x in pos]

        # Compute min and max position for levels
        minprof, maxprof = [], []
        for i in range(k):
            if len(lprof[i]) > len(minprof):
                minprof.extend([x + pos[i] for x in lprof[i][len(minprof):]])
        for i in range(k - 1, -1, -1):
            if len(rprof[i]) > len(maxprof):
                maxprof.extend([x + pos[i] for x in rprof[i][len(maxprof):]])

        # construct and return the result        
        return ((t.label(), pos), stlist), [0] + minprof, [0] + maxprof


    @staticmethod
    def get_layout(t: LabelledOrderedTree, horiz=0.7):
        r"""
        Returns a dictionary of positions of nodes in the layout (not scaled to
        any given aspect ratio). The keys of the dictionary is the node labels,
        and the values are coordinates. The layout has the root on the top. The
        tree should not have any repeated label, otherwise an error will be
        throwed.
        
        INPUT:
        - ``tree``: a LabelledOrderedTree that we want to plot
        - ``horiz``: minimal gap betwee nodes, in unity of distance between two
        consecutive layers of nodes
        """
        def depths(t, ddict, curd): # compute depth of each node
            if t.label() in ddict:
                raise ValueError('Tree should not have repeated labels')
            ddict[t.label()] = curd
            for st in t:
                depths(st, ddict, curd + 1)
        
        def shifts(s, sdict, shift): # extract shift information
            l, sfts = s[0]
            sdict[l] = shift
            for i in range(len(sfts)):
                shifts(s[1][i], sdict, shift + sfts[i])
        
        ddict = {} # dict for depth
        depths(t, ddict, 0)
        tshift = TreePlot.__compute_tree_profile(t, horiz)[0]
        sdict = {} # dict for shift
        shifts(tshift, sdict, 0)
        cdict = {} # dict for coordinates
        for label in ddict:
            cdict[label] = (sdict[label], -ddict[label]) # root on top
        return cdict

    @staticmethod
    def plot(tree, vert=1, horiz=0.7, radius=0.2, fill='lightblue',
             thickness=1.5, linecolor='black', colorfunc=None):
        r"""
        Returns a Graphics object that contains a plot of the given labeled
        tree

        INPUT:
        - ``tree``: a tree object, can be LabelledOrderedTree, OrderedTree, or
        simply a nested list representing a tree (with or without labels)
        - ``vert``: distances between nodes of consecutive depth
        - ``horiz``: minimal distance between nodes of the same depth
        - ``radius``: radius of nodes
        - ``fill``: fill color of nodes
        - ``thickness``: thickness of lines
        """
        def draw(l, t, x, y, px, py, opt):
            label, shifts = t[0]
            if label is None:
                label = ''
            # draw the root
            fcolor = opt['fill']
            if opt['cfunc'] is not None:
                fcolor = opt['cfunc'](label)
            l.append(circle((x, y), opt['radius'], fill=True,
                            facecolor=fcolor, zorder=1))
            l.append(text(str(label), (x, y), zorder=2))
            # draw the line linking to parent except for the root (y == 0)
            if y != 0:
                l.append(line([(x, y), (px, py)], zorder=0, color=opt['linec'],
                              thickness=opt['thick']))
            # draw subtrees recursively
            stlist = t[1]
            for i in range(len(stlist)):
                draw(l, stlist[i], x + shifts[i], y - opt['vert'], x, y, opt)
        
        # convert to labeled ordered tree
        t = LabelledOrderedTree(tree)
        # compute the hierarchical shifting
        tshift = TreePlot.__compute_tree_profile(t, horiz)[0]
        # initialize the graphics
        G = Graphics()
        G.set_aspect_ratio(1)
        # construct the dictionary for options
        opt = {'radius': radius, 'fill': fill, 'thick': thickness, 'vert': vert,
               'linec': linecolor, 'cfunc': colorfunc}
        # compute the graphics
        shapes = []
        draw(shapes, tshift, 0, 0, 0, 0, opt)
        for s in shapes:
            G += s
        G.axes(show=False)
        return G
