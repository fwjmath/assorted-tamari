# -*- coding: utf-8 -*-

r"""
Plotting arbitrary labeled trees

This class implement a relatively simple algorithm to plot trees in a layered
fashion. The main idea is to keep track of the left and right limits of already
plotted sub-trees, then combine them together while minimizing the size gap
"""

# ****************************************************************************
#       Copyright (C) 2023 Wenjie Fang <fwjmath@gmail.com>,
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
    def __compute_tree_profile(t: LabelledOrderedTree, horiz):
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
        # Case of leaf
        if not list(t):
            return ((t.label(), []), []), [0], [0]
        # General case
        # First, get all the info from subtrees
        stlist, lprof, rprof = [], [], []
        for st in list(t):
            newst, stlprof, strprof = TreePlot.__compute_tree_profile(st, horiz)
            stlist.append(newst)
            lprof.append(stlprof)
            rprof.append(strprof)

        # Then compute the distances and positions
        k = len(stlist)
        dist = []
        for i in range(k - 1):
            hdist = (TreePlot.__profile_distance(rprof[i], lprof[i + 1], horiz))
            dist.append(hdist)
        pos = [0]
        for d in dist:
            pos.append(pos[-1] + d)

        # Now center the root
        rootpos = pos[-1] / 2
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
        tshift, _, _ = TreePlot.__compute_tree_profile(t, horiz)
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
