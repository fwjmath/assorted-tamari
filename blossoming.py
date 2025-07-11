r'''
Tamari blossoming tree

This module implements the blossoming trees in bijection with Tamari intervals.
These blossoming trees are with half-edges bicolored following some local rules,
each node has two buds, and each edge has two legs. Buds are matched with legs
in a planar way, leaving only two dangling buds. The coloring can be replaced by
marking one of the dangling buds. The blossoming tree is represented as a plane
tree. We take the convention that the root bud is a dangling bud with red
half-edges next to it in the counter-clockwise order

REFERENCES:
Fang--Fusy--Nadeau, arXiv:2312.13159 [math.CO]
'''

# ****************************************************************************
#       Copyright (C) 2024 Wenjie Fang <fwjmath@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# ****************************************************************************
from typing import Self
from math import acos, cos, sin, pi

from sage.all import DyckWords
from sage.combinat.ordered_tree import OrderedTree, LabelledOrderedTree
from sage.combinat.binary_tree import from_tamari_sorting_tuple, BinaryTree
from sage.plot.graphics import Graphics
from sage.plot.line import line
from sage.plot.bezier_path import bezier_path
from sage.plot.circle import circle
from sage.plot.arc import arc
from sage.plot.polygon import polygon2d
from sage.plot.arrow import arrow2d
from sage.combinat.interval_posets import (TamariIntervalPoset,
                                           TamariIntervalPosets)
from sage.misc.prandom import uniform, randrange


# optional module for plotting blossoming trees
defaultlayout = 'treeplot'
try:
    from treeplot import TreePlot
except ModuleNotFoundError:
    defaultlayout = 'tree'


class TamariBlossomingTree:

    @staticmethod
    def __budcount(tree) -> int:
        r'''
        Internal function. Counts the number of buds at the root of ``tree``.
        We do not suppose ``tree`` to be of type OrderedTree
        '''
        return len([x for x in tree if not x])

    @staticmethod
    def __checkbuds(tree):
        r'''
        Internal function. Check recursively whether all nodes has two buds. We
        do not suppose ``tree`` to be of type OrderedTree.
        '''
        if not tree:
            return
        if TamariBlossomingTree.__budcount(tree) != 2:
            raise ValueError('Not a blossoming tree, bud count incorrect')
        for st in tree:
            TamariBlossomingTree.__checkbuds(st)
        return

    @staticmethod
    def __matching_word(tree) -> list[int]:
        r'''
        Internal function, returns the matching word with buds as 1 and legs as
        0. We do not suppose ``tree`` to be of type OrderedTree. We do not count
        the root here.
        '''
        def aux(tree):
            accu = []
            for t in tree:
                if not t:  # a bud
                    accu.append(1)
                else:  # not a bud, but an edge to the next subtree
                    accu.append(-1)
                    accu.extend(aux(t))
                    accu.append(-1)
            return accu

        return aux(tree)

    def __get_meandric_order(self) -> tuple[list[int], list[int]]:
        r'''
        Internal function. Computes the order of nodes and edges in the meandric
        representation. In the intermediate steps, we have

        - Buds are represented by the label of its node and 1, 2 as the order
        of buds of the same node
        - Legs are represented by the label of both its ends, and 1, 2 as the
        order of legs of the same node
        '''
        def aux(tree, budleg, budcnt):
            rlabel = tree.label()
            for st in tree:
                if not st:  # bud
                    if rlabel not in budcnt:
                        budcnt[rlabel] = 0
                    budcnt[rlabel] += 1
                    budleg.append(((rlabel,), budcnt[rlabel]))
                else:  # edge, two legs
                    budleg.append(((rlabel, st.label()), 1))
                    aux(st, budleg, budcnt)
                    budleg.append(((rlabel, st.label()), 2))
            return

        # first compute the list of buds and legs
        budleg = [((self.tree.label(),), 1)]
        budcnt = {self.tree.label(): 1}
        aux(self.tree, budleg, budcnt)

        # then match them up
        matching, stack = [], []
        for halfedge in budleg:
            if len(halfedge[0]) == 1:  # bud
                stack.append(halfedge)
            else:  # leg
                matching.append((stack.pop(), halfedge))
        if len(stack) != 2:
            raise ValueError('Error during matching: incorrect matching')

        # get it in a dictionary
        matchdict = {}
        for bud, leg in matching:
            matchdict[bud] = leg
            matchdict[leg] = bud

        # go through the dictionary to get the path, thus the order
        curnode, curord = (self.tree.label(),), 1
        morder = [curnode]
        while True:
            curord = 3 - curord  # possible values are 1 and 2
            if (curnode, curord) not in matchdict:
                break
            curedge, curord = matchdict[curnode, curord]
            morder.append(curedge)
            curord = 3 - curord
            curnode, curord = matchdict[curedge, curord]
            morder.append(curnode)

        # A last check
        if len(morder) != self.size * 2 + 1:
            raise ValueError('Error during matching: no Hamiltonian path')

        # compute both node order and edge order
        norder = [morder[i][0] for i in range(0, len(morder), 2)]
        eorder = [morder[i] for i in range(1, len(morder), 2)]

        # Finally, we return the order
        return norder, eorder

    @staticmethod
    def __canon_label(tree: OrderedTree) -> LabelledOrderedTree:
        r'''
        Internal function. Use a recursive approach to compute the canonical
        labeling of a tree without using node_number, which is very costly.
        More precisely, it is not linear, and quadratic in the worst case.
        '''
        def aux(tree: OrderedTree, curl: list[int]) -> LabelledOrderedTree:
            l: int = curl[0]
            curl[0] += 1
            return LabelledOrderedTree([aux(x, curl) for x in tree],
                                       label=l)
        return aux(tree, [1])

    def __init__(self, tree):
        r'''
        Initialize a Tamari blossoming tree with a plane tree. We consider the
        root as a bud, so every internal node has two leaves, except the root
        which has only one. We also need to check that the root is really a
        dangling node

        INPUT:
        - ``tree``: a plane tree satisfying the given condition
        '''
        # check root leaves
        if TamariBlossomingTree.__budcount(tree) != 1:
            raise ValueError('Not a blossoming tree, bud count incorrect')

        # check for all nodes
        for st in tree:
            TamariBlossomingTree.__checkbuds(st)

        # check for matching (whether the root is a dangling bud)
        mword = TamariBlossomingTree.__matching_word(tree)
        ht = 0
        for e in mword:
            ht += e
            if ht < 0:
                raise ValueError('Not a blossoming tree, bad matching')

        # all tests passed, construct the object
        # the tree, with the canonical labeling
        self.tree = TamariBlossomingTree.__canon_label(tree)
        # size is given by the number of edges in the tree (excluding buds)
        self.size = (self.tree.node_number() - 1) // 3
        # the meandric order of nodes
        self.node_order, self.edge_order = self.__get_meandric_order()
        return

    def to_plane_tree(self) -> OrderedTree:
        r'''
        Returns the blossoming tree as an OrderedTree. The buds are simply
        leaves.
        '''
        return OrderedTree(self.tree)

    def to_tamari(self) -> tuple[BinaryTree, BinaryTree]:
        r'''
        Returns the Tamari interval in bijection with ``self``, under the form
        of a pair of binary trees

        OUTPUT:
        A pair of binary trees comparable in the Tamari lattice (thus a Tamari
        interval)
        '''
        def from_dual_bracket_vector(dvec):
            if not dvec:
                return BinaryTree()
            ridx = len(dvec) - 1
            while ridx != dvec[ridx]:
                ridx -= 1
            ltree = from_dual_bracket_vector(dvec[:ridx])
            rtree = from_dual_bracket_vector(dvec[ridx + 1:])
            return BinaryTree([ltree, rtree])

        # get the orders of nodes and edges
        norder = self.node_order
        eorder = self.edge_order

        # get the bracket vector (lower) and the dual bracket vector (higher)
        bvec, dvec = [], []
        for i in range(len(eorder)):
            idx = sorted(tuple(map(lambda x: norder.index(x), eorder[i])))
            bvec.append(idx[1] - 1 - i)
            dvec.append(i - idx[0])

        # get the trees
        ltree = from_tamari_sorting_tuple(bvec)
        rtree = from_dual_bracket_vector(dvec)
        return ltree, rtree

    @staticmethod
    def from_tamari(ltree, htree) -> Self:
        r'''
        Returns the blossoming tree corresponding to the given Tamari interval,
        given as a pair of binary trees (not necessarily of type BinaryTree).

        INPUT:
        - ``ltree``, ``htree``: two binary trees such that ``ltree`` is smaller
        than ``htree`` in the Tamari order

        OUTPUT:
        A blossoming tree in bijectino with the given Tamari interval
        '''
        def traversal(node, parent, cycord):
            # internal function, which go through the tree given by cycord
            # we provide parent to know where to cut
            if node == -1:  # a bud
                return []
            children = cycord[node]
            if parent in cycord[node]:
                pidx = children.index(parent)
                children = children[pidx + 1:] + children[:pidx]
            return [traversal(x, node, cycord) for x in children]

        # initalization and verification
        btl, bth = BinaryTree(ltree), BinaryTree(htree)
        if not btl.tamari_lequal(bth):
            raise ValueError('Not a Tamari interval')

        # compute the bracket vector and the dual bracket vector
        bvec = btl.tamari_sorting_tuple()[0]
        dvec = bth.tamari_sorting_tuple(reverse=True)[0][::-1]
        n = len(bvec)

        # construct the edges between nodes, with their order
        upper = [[] for _ in range(n + 1)]  # neighbors by upper arcs
        lower = [[] for _ in range(n + 1)]  # neighbors by lower arcs
        for i in range(n):
            a, b = i - dvec[i], bvec[i] + i + 1
            upper[a].append(b)  # counter-clockwise
            lower[b].append(a)  # clockwise
        # edges in counterclockwise order (left to right for trees)
        # buds are represented by -1
        cycord = [[-1] + lower[i][::-1] + [-1] + upper[i] for i in range(n + 1)]
        # get rid of the first bud (ugly pop...)
        cycord[0].pop(0)
        # traversal for the plane tree
        # 2 saying that it is the root (so parent inexistant)
        ptree = traversal(0, -2, cycord)
        return TamariBlossomingTree(ptree)

    def to_TIP(self) -> TamariIntervalPoset:
        r'''
        Returns the corresponding TamariIntervalPoset object in bijection with
        the current blossoming tree
        '''
        t1, t2 = self.to_tamari()
        return TamariIntervalPosets.from_binary_trees(t1, t2)

    @staticmethod
    def from_TIP(tip) -> Self:
        r'''
        Returns a blossoming tree in bijection with a TamariIntervalPoset

        INPUT:
        - ``tip``: a TamariIntervalPoset object representing a Tamari interval
        '''
        t1, t2 = tip.lower_binary_tree(), tip.upper_binary_tree()
        return TamariBlossomingTree.from_tamari(t1, t2)

    @staticmethod
    def binary_tree_plot(btree) -> Graphics:
        r'''
        Utility function for plotting binary trees in the Chapoton way

        INPUT:
        - ``btree``: a binary tree, not necessarily of type BinaryTree

        OUTPUT:
        A plot of ``btree``, with leaves on a horizontal line, and edges all of
        slope +1 or -1. Labels are ignored.
        '''
        # auxiliary function to compute coordinates of internal nodes
        def aux(t, a, b, points):
            if t.is_empty():
                return
            # current point
            points.append(((a + b) / 2, (b - a) / 2))
            # recursive calls
            lt, rt = tuple(list(t))
            lsize = lt.node_number()
            aux(lt, a, a + lsize, points)
            aux(rt, a + lsize + 1, b, points)
            return

        # initialization
        bt = BinaryTree(btree)
        n = bt.node_number()
        G = Graphics()
        G.set_aspect_ratio(1)

        # get node positions
        points = []
        aux(bt, 0, n, points)

        # plot, first leaves, then nodes and edges
        for i in range(n + 1):
            G += circle((i, 0), 0.05, fill=True, zorder=2)
        for x, y in points:
            G += circle((x, y), 0.2, fill=True, facecolor='white', zorder=2)
            G += line([(x, y), (x + y, 0)], zorder=1, thickness=1)
            G += line([(x, y), (x - y, 0)], zorder=1, thickness=1)
        G.axes(show=False)
        return G

    def tamari_dual(self) -> Self:
        r'''
        Perform the half-turn symmetric on meandric tree and return the result.
        This is equivalent of taking the dual in the Tamari lattice for the
        corresponding interval. Not to be confused with the mirror symmetric of
        blossoming trees.

        Note that we use a feature of from_plane_tree instead of using the usual
        Tamari module already in Sagemath to avoid exceeding the number of
        recursions during the left-right symmetry of the binary trees when tree
        size is large.
        '''
        # use the fact that from_plane_tree picks the bud with the opposite
        # color of the root, so exchanges the color (thus duality)
        return TamariBlossomingTree.from_plane_tree(self.tree)

    def plot_meandric(self, semicircle=False, arrow=True) -> Graphics:
        r'''
        Plot the meandric tree of ``self``

        INPUT:
        - ``semicircle``: optional, sets whether the arcs are drawn as
        semicircles
        - ``arrow``: optional, sets whether draw horizontal arrows tips.
        '''
        def sqnode(x, y):
            diam = 0.1
            return polygon2d([[x - diam, y - diam], [x + diam, y - diam],
                              [x + diam, y + diam], [x - diam, y + diam]],
                             edgecolor='black', rgbcolor='white', zorder=2)

        def cirnode(x, y):
            return circle([x, y], 0.15, fill=True, edgecolor='black',
                          facecolor='black', zorder=2)

        def semicir(x1, x2, isupper):
            sec = (0, pi) if isupper else (pi, 2 * pi)
            color = 'blue' if isupper else 'red'
            return arc([(x1 + x2) / 2, 0], (x2 - x1) / 2, sector=sec, zorder=1,
                       rgbcolor=color)

        def bezierarc(x1, x2, isupper):
            cp1 = [x1 * 0.7 + x2 * 0.3, (x2 - x1) * 0.6]
            cp2 = [x1 * 0.3 + x2 * 0.7, (x2 - x1) * 0.6]
            if not isupper:
                cp1[1], cp2[1] = -cp1[1], -cp2[1]
            cp1 = tuple(cp1)
            cp2 = tuple(cp2)
            color = 'blue' if isupper else 'red'
            return bezier_path([[(x1, 0), cp1, cp2, (x2, 0)]], zorder=1,
                               rgbcolor=color)

        # initialization
        G = Graphics()
        G.set_aspect_ratio(1)
        arcfct = semicir if semicircle else bezierarc

        # draw the vertices, black circle for tree node, white squares for edges
        n = self.size
        for i in range(2 * n + 1):  # tree nodes
            if i % 2 == 0:
                G += cirnode(i, 0)
                if arrow:
                    G += arrow2d((i, 0), (i + 0.6, 0), rgbcolor='black',
                                 width=1, arrowsize=2)
                    G += arrow2d((i, 0), (i - 0.6, 0), rgbcolor='black',
                                 width=1, arrowsize=2)
                else:
                    G += line([(i, 0), (i + 0.6, 0)], rgbcolor='black')
                    G += line([(i, 0), (i - 0.6, 0)], rgbcolor='black')
            else:
                G += sqnode(i, 0)

        # draw the arcs (tree edges), depending on options
        norder, eorder = self.node_order, self.edge_order
        for i in range(n):
            nidx1, nidx2 = eorder[i]
            k, m = sorted((norder.index(nidx1), norder.index(nidx2)))
            G += arcfct(k * 2, i * 2 + 1, True)   # upper arc
            G += arcfct(i * 2 + 1, m * 2, False)  # lower arc
        G.axes(show=False)
        return G

    @staticmethod
    def __find_dangling_bud(tree: LabelledOrderedTree) -> list[int]:
        r'''
        Internal function. Returns the dangling buds of ``tree``, in the order
        of counterclockwise order starting from the root. In ``tree`` we assume
        that there is a bud for the root (that is not in ``tree``), labeled 0
        (which should not be in canonical labeling of ``tree``).
        '''
        def aux(t, buds, dyck):
            for st in t:
                if not st:  # bud
                    buds.append(st.label())
                    dyck.append(1)
                else:  # edge and subtree
                    dyck.append(-1)
                    aux(st, buds, dyck)
                    dyck.append(-1)
            return

        buds = [0]  # the root bud
        dyck = [1]  # the root bud
        aux(tree, buds, dyck)

        # find the latest lowest point
        lowest, lidx, height = 0, 0, 0
        for i in range(len(dyck)):
            height += dyck[i]
            if height <= lowest:
                lowest, lidx = height, i + 1
        # find the corresponding bud
        budcnt = dyck[:lidx].count(1)
        # splice to get a walk above 0, go for the latest point with height 1
        ndyck = dyck[lidx:] + dyck[:lidx]
        oneidx, height = 0, 0
        for i in range(len(ndyck)):
            height += ndyck[i]
            if height == 1 and ndyck[i] < 0:
                oneidx = i
        oneidx += lidx
        if oneidx > len(ndyck):
            oneidx -= len(ndyck)
        budcnt2 = dyck[:oneidx].count(1)
        return [buds[budcnt], buds[budcnt2]]

    @staticmethod
    def __get_cycle_order(t: LabelledOrderedTree) -> list[int]:
        r'''
        Internal function. Returns the cyclic order (in the sens of maps) of the
        given tree. More precisely, this functions returns a dictionary with
        node labels as keys and a (cyclic) list of its neighbors in
        counterclockwise order. The root bud is labeled 0, under the assumption
        that 0 is not present in the canonical labeling.
        '''
        def aux(tree, parent, cycord):
            cycord[tree.label()] = [parent] + [st.label() for st in tree]
            for st in tree:
                aux(st, tree.label(), cycord)

        cycord = {}
        cycord[0] = [t.label()]
        aux(t, 0, cycord)
        return cycord

    @staticmethod
    def from_plane_tree(tree, skip_check=False, random_bud=False) -> Self:
        r'''
        Return the blossoming tree corresponding to the given tree. We suppose
        that the root of the tree is a bud. Comparing to __init__, we do not
        fail when the buds are not matching, but tries to find the correct bud.
        We assume that the root, which is a bud, has red half-edges next to it
        in counter-clockwise order (so the left one). We then find the unpaired
        bud with the opposite property, to simplify the reflection operation.

        INPUT:
        - ``tree``: a plane tree with two buds on each node (one for the root).
        - ``skip_check``: skip checking for bud conditions
        - ``random_bud``: choose a bud at random, instead of the first
        '''
        def traverse(node, parent, cycord):
            # Internal function, construct a plane tree out of the cycle order
            # provide parent to know where to cut
            pidx = cycord[node].index(parent)
            stnodes = cycord[node][pidx + 1:] + cycord[node][:pidx]
            return [traverse(stn, node, cycord) for stn in stnodes]

        # check buds
        if not skip_check:
            if TamariBlossomingTree.__budcount(tree) != 1:
                raise ValueError('Not a blossoming tree, bud count incorrect')
            for st in tree:
                TamariBlossomingTree.__checkbuds(st)

        tree = TamariBlossomingTree.__canon_label(tree)
        dangling = TamariBlossomingTree.__find_dangling_bud(tree)

        # compute bud color
        cycord = TamariBlossomingTree.__get_cycle_order(tree)
        dcolor = [0, 0]
        for i in range(2):
            bud = dangling[i]
            if bud == 0:
                dcolor[i] = 0
                continue
            color = 0
            curpos = bud
            while curpos != 0:  # going up to the root
                prevpos = curpos
                curpos = cycord[curpos][0]
                pidx = cycord[curpos].index(prevpos)
                for sibling in cycord[curpos][pidx + 1:]:
                    if len(cycord[sibling]) == 1:  # a bud
                        color = 1 - color
                color = 1 - color  # going to the opposite half-edge
            dcolor[i] = 1 - color  # accounting for the root bud

        # select against colors
        if sum(dcolor) != 1:
            raise ValueError('Invalide blossoming tree: bud colors')
        didx = dcolor.index(1)  # select the opposite color
        if random_bud:
            didx = randrange(2)
        dangling = dangling[didx]
        rroot = cycord[dangling][0]  # the only neighbor of a bud is the root
        rtree = traverse(rroot, dangling, cycord)
        return TamariBlossomingTree(rtree)  # can do with a list

    def reflection(self) -> Self:
        r'''
        Return the blossoming tree that is the mirror image of the current
        blossoming tree. Note that the dangling buds change in general, so the
        root dangling bud will be the one with the correct color.

        OUTPUT:
        A blossoming tree that is the mirror image of the current one. Not to be
        confused with the Tamari dual.
        '''
        tree = self.to_plane_tree().left_right_symmetry()
        return TamariBlossomingTree.from_plane_tree(tree, skip_check=True)

    def plot_blossoming(self, aspect=1.0, layout=None) -> Graphics:
        r'''
        Plot the blossoming tree of ``self``, using the plot of OrderedTree, but
        with buds well spaced.

        INPUT:
        - ``aspect``: ratio of aspect, default to 1.0
        - ``layout``: the algorithm for layout, with three possible options:
            * 'treeplot': uses ``get_layout`` in ``TreePlot`` (default)
            * 'tree': uses ``layout_tree`` of undirected graph in sage
            * 'planar': uses ``layout_planar`` of undirected graph in sage
        '''
        def euclid_dist(p1, p2):
            return sum([(p1[i] - p2[i]) ** 2 for i in range(2)]) ** 0.5

        def rad_dir(p1, p2):
            plen = euclid_dist(p1, p2)
            p = [(p2[i] - p1[i]) / plen for i in range(2)]
            r = acos(p[0])
            if p[1] < 0:
                r = -r
            return r

        def shift_point(p, rad, dist):
            px = p[0] + cos(rad) * dist
            py = p[1] + sin(rad) * dist
            return (px, py)

        def plot_bud(origp, rad, m, bud, dbuds):
            p2 = shift_point(pos[rn], rad, m)
            w = 1
            color = 'red'
            if bud == dbuds[0]:
                w = 3
                color = 'darkgreen'
            elif bud == dbuds[1]:
                w = 2
                color = 'darkgreen'
            return line([pos[rn], p2], rgbcolor=color, thickness=w, zorder=1)

        # construct the graph and the embedding
        t = LabelledOrderedTree([self.tree], label=0)
        cycord = TamariBlossomingTree.__get_cycle_order(self.tree)
        degs = [len(cycord[x]) for x in cycord]
        n = len(cycord)
        realnodes = [i for i in range(n) if degs[i] > 1]
        g = t.to_undirected_graph()
        # using clockwise direction, instead of counterclockwise for trees
        embed = {x: cycord[x][::-1] for x in cycord}
        g.set_embedding(embed)
        # use appropriate layout algorithm
        pos = None
        if layout is None:
            layout = defaultlayout
        if layout == 'treeplot':
            if defaultlayout != 'treeplot':
                raise ModuleNotFoundError('Module Treeplot absent')
            pos = TreePlot.get_layout(t)
        elif layout == 'tree':
            pos = g.layout_tree()
        elif layout == 'planar':
            pos = g.layout_planar(on_embedding=embed, external_face=(0, 1))
        else:
            raise ValueError('Invalid option for parameter "layout"')

        # Initialize the graphic
        G = Graphics()
        G.set_aspect_ratio(aspect)

        # Normalize node positions
        xcoords = [pos[i][0] for i in realnodes]
        minx = min(xcoords)
        maxx = max(xcoords)
        ycoords = [pos[i][1] for i in realnodes]
        miny = min(ycoords)
        maxy = max(ycoords)
        multfact = aspect / (maxy - miny) * (maxx - minx)
        for node in realnodes:
            e = pos[node]
            pos[node] = (e[0], (e[1] - miny) * multfact + miny)

        # compute min edge for scaling (excluding buds)
        minedge = None
        for n1 in realnodes:
            for n2 in [i for i in cycord[n1] if degs[i] > 1]:
                edlen = euclid_dist(pos[n1], pos[n2])
                if minedge is None or minedge > edlen:
                    minedge = edlen

        # draw the real nodes (not the buds)
        for node in realnodes:
            G += circle(pos[node], 0.02 * edlen, fill=True, zorder=2)

        # draw the real edges
        for n1 in realnodes:
            for n2 in [i for i in cycord[n1] if degs[i] > 1 and i > n1]:
                G += line([pos[n1], pos[n2]], zorder=1, thickness=1)

        # draw the buds
        dbuds = TamariBlossomingTree.__find_dangling_bud(self.tree)
        budlen = minedge * 0.3
        for rn in realnodes:
            ncnt = len(cycord[rn])
            budidx = [i for i in range(ncnt) if degs[cycord[rn][i]] == 1]
            if budidx[1] - budidx[0] in [1, ncnt - 1]:  # two consecutive buds
                rad1 = rad_dir(pos[rn], pos[cycord[rn][budidx[0] - 1]])
                eidx2 = budidx[1] + 1 - ncnt  # using negative index for cyclic
                rad2 = rad_dir(pos[rn], pos[cycord[rn][eidx2]])
                if rad2 <= rad1:
                    rad2 += pi * 2
                # trisection of angle
                rbuds = [rad1 + (rad2 - rad1) / 3 * (1 + i) for i in range(2)]
                for i in range(2):
                    G += plot_bud(pos[rn], rbuds[i], budlen,
                                  cycord[rn][budidx[i]], dbuds)
            else:  # two non-consecutive buds, we put each one in the middle
                for i in range(2):
                    rad1 = rad_dir(pos[rn], pos[cycord[rn][budidx[i] - 1]])
                    eidx2 = budidx[i] + 1 - ncnt
                    rad2 = rad_dir(pos[rn], pos[cycord[rn][eidx2]])
                    if rad2 <= rad1:
                        rad2 += pi * 2
                    rbud = (rad1 + rad2) / 2
                    G += plot_bud(pos[rn], rbud, budlen,
                                  cycord[rn][budidx[i]], dbuds)

        # output
        G.axes(show=False)
        return G

    @staticmethod
    def __binary_tree_arcs(btree: BinaryTree) -> list[tuple[int]]:
        '''
        Internal function. Returns the list of arcs in the smooth drawing of a
        given binary tree.

        INPUT:
        - ``btree``: a binary tree, which can be a BinaryTree or an
                       OrderedTree that happens to be binary

        OUTPUT:
        The list of arcs in the smooth drawing, represented by leaves on its
        both ends.
        '''
        def aux(bt, offset, arcs):
            if not bt:
                return
            arcs.append((offset, offset + bt.node_number()))
            stlist = list(bt)
            aux(stlist[0], offset, arcs)
            aux(stlist[1], offset + stlist[0].node_number() + 1, arcs)

        arclist = []
        aux(btree, 0, arclist)
        return arclist

    @staticmethod
    def binary_tree_smooth_drawing(btree, color='blue') -> Graphics:
        r'''
        Utility function for plotting the smooth drawing of a binary tree

        INPUT:
        - ``btree``: a binary tree, not necessarily of type BinaryTree
        - ``color``: color of the arcs

        OUTPUT:
        The smooth drawing of a binary tree with the given color
        '''
        # initialization
        bt = BinaryTree(btree)
        G = Graphics()
        G.set_aspect_ratio(1)

        # plot the arcs
        for e in TamariBlossomingTree.__binary_tree_arcs(bt):
            G += arc([(e[0] + e[1]) / 2, 0], (e[1] - e[0]) / 2, sector=(0, pi),
                     rgbcolor=color)
        G.axes(show=False)
        return G

    def smooth_drawing(self) -> Graphics:
        r'''
        Plot the smooth drawing of ``self``
        '''
        def cirnode(x, y):
            return circle([x, y], 0.1, fill=True, edgecolor='black',
                          facecolor='black', zorder=2)

        def semicir(x1, x2, isupper):
            sec = (0, pi) if isupper else (pi, 2 * pi)
            color = 'blue' if isupper else 'red'
            return arc([(x1 + x2) / 2, 0], (x2 - x1) / 2, sector=sec, zorder=1,
                       rgbcolor=color)

        # initialization
        G = Graphics()
        G.set_aspect_ratio(1)

        # draw the vertices, black circle for tree node, white squares for edges
        n = self.size
        for i in range(n + 1):  # tree nodes
            G += cirnode(i, 0)

        # draw the arcs according to upper and lower trees
        trees = self.to_tamari()
        for i in range(2):
            for e in TamariBlossomingTree.__binary_tree_arcs(trees[i]):
                G += semicir(e[0], e[1], i == 1)  # 0 is lower, 1 is upper
        G.axes(show=False)
        return G

    def is_synchronized(self) -> bool:
        r'''
        Returns whether the Tamari interval presented by the current blossoming
        tree is synchronized, i.e., two buds of the same node are adjacent.

        OUTPUT:
        ``True`` if the blossoming tree is synchronized, and ``False`` otherwise
        '''
        def aux(tree, isroot=False):
            '''
            Check synchronized condition on subtree
            '''
            # get indices of buds
            idx = [i for i in range(len(tree)) if not tree[i]]
            # bud number, and consecutive check
            if isroot:
                # at the root: one bud at the beginning or the end
                if len(idx) != 1 or (idx[0] != 0 and idx[0] != len(tree) - 1):
                    return False
            else:
                # otherwise: two buds consecutive
                if len(idx) != 2 or idx[1] - idx[0] != 1:
                    return False
            for st in tree:
                if not st and not aux(st):  # an internal node failing the test
                    return False
            return True
        return aux(self.tree, isroot=True)

    def is_modern(self) -> bool:
        r'''
        Returns whether the Tamari interval associated to the current blossoming
        tree is modern, using the function ``is_modern`` in TamariIntervalPoset.

        OUTPUT:
        ``True`` if the blossoming tree is modern, and ``False`` otherwise
        '''
        return self.to_TIP().is_modern()


class RandomPath:
    r'''
    This class contains static functions related to the generation of random
    positive lattice paths with steps (1, k - 1) and (1, -1) of length kn + 1,
    which can be negative only at the end of the last step, with n and k given
    in parameters.
    '''

    @staticmethod
    def gen_comb(n: int, k: int) -> list[int]:
        r'''
        Generate a random combination of n elements among kn + 1 elements using
        a random approach, which is faster than the unranking approach.

        INPUT:
        - ``n``: a positive integer
        - ``k``: a strictly positive integer at least 2

        OUTPUT:
        A list of elements in the random combination of ``n`` elements among
        integers from ``1`` to ``kn+1``, not necessary in order.
        '''
        # test validity
        if n < 0 or k <= 1:
            raise ValueError("Invalid parameter")
        # get a random set with each element appearing with prob 1/k
        # the size of the set is close to n, with sqrt(n) standard deviation
        # better than unranking in terms of performance
        s: list[int] = []   # the random set
        cs: list[int] = []  # its complement
        for i in range(k * n + 1):
            if randrange(k) == 1:
                s.append(i)
            else:
                cs.append(i)
        cnt: int = len(s)
        if cnt > n:  # First case: too many elements
            # remove randomly until getting the correct number
            while cnt > n:
                s[randrange(cnt)] = s[-1]
                s.pop()
                cnt -= 1
        else:
            # add elements randomly until getting the correct number
            while cnt < n:
                id: int = randrange(k * n + 1 - cnt)
                s.append(cs[id])
                cs[id] = cs[-1]
                cs.pop()
                cnt += 1
        return s

    @staticmethod
    def cutting(cardlist: list[float], size: int) -> list[(float, int)]:
        '''
        Generate the cutting ratio list according to a list of (relative) count
        of objects of sizes from ``0`` to ``size``. The cutting ratio list tells
        us the probability to generate pairs of each size separation.

        INPUT:
        - ``cardlist``: a list of the cardinality of objects of sizes from
        ``0`` to ``size``
        - ``size``: the size of elements to generate
        '''
        # check list size
        if len(cardlist) != size + 1:
            raise ValueError("Invalid parameter: l does not have correct size.")
        cutting: list[(float, int)] = []
        for i in range(size + 1):
            cutting.append((cardlist[i] * cardlist[size - i], i))
        cutting.sort(key=lambda x: x[0], reverse=True)
        return cutting

    @staticmethod
    def comb_to_path(n: int, k: int, uset: list[int]) -> list[int]:
        path = [-1] * (k * n + 1)
        for e in uset:
            path[e] = k - 1
        # find last lowest point
        lidx, minh, height = 0, 0, 0
        for i in range(len(path)):
            height += path[i]
            if height < minh:
                lidx, minh = i + 1, height
        # rotate for the path
        path = path[lidx:] + path[:lidx]
        # remove last step
        path.pop()
        return path

    @staticmethod
    def gen_path(n: int, k: int) -> list[int]:
        r'''
        Internal function. Returns a path for 3-ary trees (4n+1 steps, n of them
        up steps, then last step removed).
        '''
        uset = RandomPath.gen_comb(n, k)
        return RandomPath.comb_to_path(n, k, uset)


class TamariBlossomingTreeFactory:
    r'''
    This factory class is for random generation of Tamari blossoming trees of
    given size. As some precomputation is done, it would be the best to keep an
    instance of this factory if users want to generate many objects of the same
    size.
    '''

    def __init__(self, size: int):
        r'''
        Initialization.

        INPUT:
        - ``size``: the size of blossoming trees to generate, that is, the
        number of edges (not counting buds)
        '''
        if size <= 0:
            raise ValueError('Invalid parameter size.')
        self.size = size
        # compute the size of trees
        # normalized by dividing the growth factor 4^4 / 3^3
        # precision is enough, as the rest grows as n^(-3/2)
        l: list[float] = [1.0]  # no need to use numerical_approx with prec
        for i in range(1, size + 1):
            nextitem = l[-1] * (4 * i - 1) * (4 * i - 2) * (4 * i - 3) / 64
            nextitem /= (3 * i + 1) * i * (3 * i - 1) / 9
            l.append(nextitem)
        # counting for generation
        self.cutting = RandomPath.cutting(l, size)
        self.cutting_sum = sum([x[0] for x in self.cutting])

    def _rand_path(self) -> list[int]:
        r'''
        Internal function. Returns a path for the correct trees, using counting.
        '''
        # get the correct size separation
        cnt = uniform(0, self.cutting_sum)
        s1, s2 = -1, -1
        for e in self.cutting:
            if cnt < e[0]:
                s1 = e[1]
                break
            else:
                cnt -= e[0]
        s2 = self.size - s1
        p1 = RandomPath.gen_path(s1, 4)
        p2 = RandomPath.gen_path(s2, 4)
        return [3] + p1 + [-1] + p2 + [-1, -1]

    @staticmethod
    def _path_to_tree(path: list[int]) -> list[list[int]]:
        r'''
        Internal function. Returns a nearly blossoming tree (without closure
        condition) from the given path ``path`` for 4-ary trees. We assume that
        the given path is valid (4n+1 steps, n of them up steps, ending at -1).

        Half-public for testing
        '''
        stack = [[0, []]]
        for step in path:
            if step == 3:  # new node
                stack.append([0, []])
            else:  # depending on type
                if stack[-1][0] < 2:  # add bud
                    stack[-1][0] += 1
                    stack[-1][1].append([])
                else:  # subtree completed
                    subtree = stack.pop()[1]
                    stack[-1][1].append(subtree)

        # Get the tree (list of subtrees for the moment)
        stack = stack[-1][1][0]
        # pop the last bud, which is always the last child
        stack.pop()
        return stack

    def random_element(self) -> TamariBlossomingTree:
        r'''
        Generate a random blossoming tree of a given size
        '''
        path = self._rand_path()
        tree = TamariBlossomingTreeFactory._path_to_tree(path)
        return TamariBlossomingTree.from_plane_tree(tree, skip_check=True,
                                                    random_bud=True)


class SynchronizedBlossomingTreeFactory:
    r'''
    This factory class is for random generation of synchronized blossoming
    trees, which are in bijection with modern Tamari intervals, of a given
    size. No precomputation is needed here, but we keep the same convention.

    We note that synchronized blossoming trees come with the two buds of the
    same node always consecutive, and we simplify them by identifying them.
    '''
    def __init__(self, size: int):
        r'''
        Initialization

        INPUT:
        - ``size``: the size of the synchronized blossoming tree to generate.
        '''
        if size <= 0:
            raise ValueError('Invalid parameter size.')
        self.size = size

    @staticmethod
    def __rand_tree(size) -> list[list[int]]:
        r'''
        Internal function. Returns a random tree with buds identified

        TODO: bug here
        '''
        path = RandomPath.gen_path(size, 3)
        stack = [[0, []]]
        for step in path:
            if step == 2:  # new nodes
                stack.append([0, []])
            else:  # depending on type
                if stack[-1][0] == 0:  # add two buds
                    stack[-1][0] = 1
                    stack[-1][1].append([])
                    stack[-1][1].append([])
                else:  # subtree completed
                    subtree = stack.pop()[1]
                    stack[-1][1].append(subtree)
        tree = stack[-1][1]
        tree.append([])  # add the extra bud besides the root
        return tree

    def random_element(self) -> TamariBlossomingTree:
        r'''
        Generate a random synchronized blossoming tree of a given size
        '''
        tree = SynchronizedBlossomingTreeFactory.__rand_tree(self.size)
        return TamariBlossomingTree.from_plane_tree(tree, skip_check=True,
                                                    random_bud=True)


class ModernBlossomingTreeFactory:
    r'''
    This factory class is for the generation of blossoming trees associated with
    modern Tamari intervals of a given size. As some precomputation is needed,
    it is the best practice to keep the same instance when generating multiple
    modern blossoming trees.

    According to Section 5.5 of the article, the generating function of modern
    blossoming trees can be written as (1 + C)^2, with:

    - C = A / (1 - B)
    - B = z / (1 - B) * (1 + C)
    - A = z / (1 - B) * (1 + C)^2 = B * (1 + C)

    By solving it, we know that

    - C is the series of Dyck paths with weight 2 on every non-initial up-step
    - B is the series of Dyck paths of C without touching the x-axis in middle
    - A is the series of Dyck paths with weight 2 on every up-step except the
    first and the second one on the x-axis (there may be only one such step)
    '''
    def __init__(self: Self, size: int):
        r'''
        Initialization and precomputation

        INPUT:
        - ``size``: the size of modern blossoming trees to generate, which is
        the number of internal edges (not including buds)
        '''
        if size <= 0:
            raise ValueError('Invalid parameter size.')
        self.size = size
        # compute the size of trees
        # two parts, each given by the series
        # 1 + C(z) = 1 + \sum_{n \geq 1} \frac{2^{n-1}}{n+1} \binom{2n}{n} z^n
        # growth rate 8^n
        l: list[float] = [8.0, 1.0]  # float suffices as for other families
        for i in range(2, size + 1):
            l.append(l[-1] * (i - 0.5) / (i + 1))
        # counting for generation
        self.cutting = RandomPath.cutting(l, size)
        self.cutting_sum = sum([x[0] for x in self.cutting])

    @staticmethod
    def __genC(dtree: OrderedTree) -> list[OrderedTree]:
        r'''
        Internal function. Generate a forest counted by the series 1+C, which
        is a sequence of B-trees followed by an A-tree, given a Dyck path and
        the colors of the up-steps on the x-axis. We represent the Dyck path by
        a plane tree so that the colors can be generated on the fly.

        INPUT:
        - `dtree`: a plane tree standing for the Dyck path

        OUTPUT:
        A list of corresponding trees
        '''
        if not dtree:  # empty tree
            return []
        if len(dtree) == 1 and not dtree[0]:  # simple tree
            return [OrderedTree([[], []])]
        idx = len(dtree) - 1  # index of cutting
        while idx > 0:  # never check the first
            if randrange(2) == 1:  # bad color, B stops here
                break
            idx -= 1
        idx += 1
        lasttree = ModernBlossomingTreeFactory.__genA(OrderedTree(dtree[:idx]))
        treelist = [lasttree]
        restlist = [ModernBlossomingTreeFactory.__genB(dtree[i])
                    for i in range(idx, len(dtree))]
        treelist.extend(restlist)
        return treelist

    @staticmethod
    def __genB(dtree: OrderedTree) -> OrderedTree:
        r'''
        Internal function. Generate a B-tree, given a Dyck path counted by the
        series B (colors generated on the fly). The Dyck path (without the
        initial and final step) is represented by a plane tree.

        INPUT:
        - `dtree`: a plane tree standing for the Dyck path with first and last
        step removed

        OUTPUT:
        The corresponding B-tree
        '''
        if not dtree:  # empty tree
            return OrderedTree([[], []])
        idx = 0  # index of cutting
        while idx < len(dtree):
            if randrange(2) == 1:  # bad color, B stops here
                break
            idx += 1
        # first sequence: a sequence of B
        treelist = [ModernBlossomingTreeFactory.__genB(dtree[i])
                    for i in range(idx)]
        # the first bud
        treelist.append(OrderedTree([]))
        # second sequence: a sequence given by C
        restlist = ModernBlossomingTreeFactory.__genC(OrderedTree(dtree[idx:]))
        treelist.extend(restlist)
        # the second bud
        treelist.append(OrderedTree([]))
        return OrderedTree(treelist)

    @staticmethod
    def __genA(dtree: OrderedTree) -> OrderedTree:
        r'''
        Internal function. Generate an A-tree, given a Dyck path counted by the
        series A with colors given on the fly (so no color for two up-steps).
        The Dyck path is again given as a plane tree.

        INPUT:
        - `dtree`: a plane tree standing for the Dyck path

        OUTPUT:
        The corresponding A-tree
        '''
        if not dtree:  # empty tree, should not happen!
            raise ValueError('Internal error on __genA')
        # first part: same as B, and there is already a separating bud
        treelist = [x for x in ModernBlossomingTreeFactory.__genB(dtree[0])]
        # second part: a sequence from C
        restlist = ModernBlossomingTreeFactory.__genC(OrderedTree(dtree[1:]))
        treelist.extend(restlist)
        return OrderedTree(treelist)

    def random_element(self) -> TamariBlossomingTree:
        r'''
        Generate a random modern blossoming tree of a given size
        '''
        # get the size separation
        cnt = uniform(0, self.cutting_sum)
        s1, s2 = -1, -1
        for e in self.cutting:
            if cnt < e[0]:
                s1 = e[1]
                break
            else:
                cnt -= e[0]
        s2 = self.size - s1
        # first C sequence
        l1 = self.__genC(DyckWords(s1).random_element().to_ordered_tree())
        # a bud
        l1.append(OrderedTree([]))
        # second C sequence
        l2 = self.__genC(DyckWords(s2).random_element().to_ordered_tree())
        l1.extend(l2)
        tree = OrderedTree(l1)
        return TamariBlossomingTree.from_plane_tree(tree, skip_check=True,
                                                    random_bud=True)
