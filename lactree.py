# -*- coding: utf-8 -*-

r"""
Left-aligned colorable trees

This module implements left-aligned colorable trees, which are parabolic Catalan
objects. They were introduced in [CFM2019]_, and are in bijection with various
other parabolic Catalan objects.

REFERENCES:

.. [CFM2019] Cesar Ceballos, Wenjie Fang, Henri Mühle.
   *The Steep-Bounce Zeta Map in Parabolic Cataland*
   Preprint. (2019). :arxiv: `1903.08515`.
"""

# ****************************************************************************
#       Copyright (C) 2019 Wenjie Fang <fwjmath@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# ****************************************************************************

from sage.combinat.ordered_tree import LabelledOrderedTree, OrderedTree
from sage.combinat.dyck_word import DyckWord

class LACTree:
    
    r"""
    Checks if T is compatible with alpha. If so, a color vector is returned. 
    Otherwise, None is returned.
    
    INPUT:
    
    - ``T`` -- an ordered tree
    - ``alpha`` -- a composition indicating colors
    
    OUTPUT:
    
    A pair ``(Tc, color)`` with ``Tc`` the same tree with canonical labeling, 
    and ``color`` the color vector
    """
    @staticmethod
    def __coloring__(T, alpha):
        n = sum(alpha)
        if n+1 != T.node_number():
            raise ValueError('Inconsistent sizes of parameters')

        #initialization
        Tc = T.canonical_labelling()
        color = [-1] * (n+2)
        stack = list(Tc)
        stack.reverse()

        #iteration (stack goes in reversed order)
        for i in range(len(alpha)):
            if len(stack) < alpha[i]:
                return None
            tocolor = []
            for j in range(alpha[i]):
                tocolor.append(stack.pop())
            for j in range(alpha[i]):
                st = tocolor.pop()
                color[st.label()] = i
                newlist = list(st)
                newlist.reverse()
                stack += newlist

        #return
        return (Tc, color)
    
    r"""
    Constructor of the class, checks if the parameters are compatible
    
    INPUT:
    
    - ``T``: an ordered tree
    - ``alpha``: a composition indicating the number of nodes for each color
    
    OUTPUT:
    
    If the input is compatible, then return an object of ``LACTree``
    """
    def __init__(self, T, alpha):
        check = self.__coloring__(T,alpha)
        if check is None:
            raise ValueError('Incompatible parameters')
        else:
            self.tree, self.color = check
            self.alpha = alpha
    
    r"""
    Shows a pdf file of the LAC-tree (because Sagemath cannot plot a tree with
    repeated labels)
    """
    def plot(self):
        # Sage not yet able to plot a tree with repeating labels!
        view(self.tree.map_labels(lambda x: self.color[x]))
        return

    r"""
    Returns an LAC-tree in bijection with the given bounce pair. A check is
    performed for validity.
    
    INPUT:
    
    - ``dyck``: a Dyck path in the 0,1 format
    - ``alpha``: a composition indicating the bounce path
    
    OUTPUT:
    
    An LAC-tree in bijection with this bounce pair
    """
    @staticmethod
    def from_bounce_pair(dyck, alpha):
        n = sum(alpha)
        if n*2 != len(dyck):
            raise ValueError('Inconsistent sizes of parameters')
        bounce = []
        for a in alpha:
            bounce += ([1] * a) + ([0] * a)
        dwa = DyckWord(dyck)
        dwb = DyckWord(bounce)
        area_a = dwa.to_area_sequence()
        area_b = dwb.to_area_sequence()
        if not all(area_a[i] >= area_b[i] for i in range(n)):
            raise ValueError('Incompatible parameters')

        # count children number by counting north steps on each x-coordinate
        vsteps = [0] * (n+1)
        cur = 0
        x = 0
        while cur < len(dyck):
            while 1 == dyck[cur]:
                cur += 1
                vsteps[x] += 1
            cur += 1
            x += 1

        # construct tree
        l = len(alpha)
        dyckpost = n - alpha[l-1]
        actives = [OrderedTree([]) for i in range(alpha[l-1])]
        for region in range(l-2,-1,-1):
            newactives = []
            for i in range(alpha[region]):
                newnode = OrderedTree(actives[:vsteps[dyckpost]])
                actives = actives[vsteps[dyckpost]:]
                newactives.append(newnode)
                dyckpost -= 1
            actives = newactives + actives
        T = OrderedTree(actives)
        
        # coloring with existent function
        
        return LACTree(T, alpha)
    
    r"""
    Returns a bounce pair in bijection with the LAC-tree
    
    OUTPUT:
    
    A pair ``(path, alpha)``, where ``path`` is a Dyck path in 0,1 format,
    and ``alpha`` the composition of the bounce path.
    """
    def to_bounce_pair(self):
        n = sum(self.alpha)
        l = len(self.alpha)
        path = [1] * len(self.tree)
        cvec = [[] for i in range(l+1)]
        for x in self.tree.pre_order_traversal_iter():
            cvec[self.color[x.label()]].append(len(x))
        for i in range(l):
            cvec[i].reverse()
            for k in cvec[i]:
                path += [0]
                path += [1] * k
        return (path, self.alpha)
    
    r"""
    Returns an LAC-tree in bijection with the given steep pair. A check is
    performed for validity.
    
    INPUT:
    
    - ``steep``: a steep path in the 0,1 format
    - ``path``: a Dyck path in the 0,1 format
    
    OUTPUT:
    
    An LAC-tree in bijection with this steep pair
    """
    @staticmethod    
    def from_steep_pair(steep, path):
        if len(steep) != len(path):
            raise ValueError('Inconsistent sizes of parameters')
        n = len(path) // 2
        a1 = DyckWord(steep).to_area_sequence()
        a2 = DyckWord(path).to_area_sequence()
        for i in range(len(a1)):
            if a1[i] < a2[i]:
                raise ValueError('Incompatible parameters: not nested')
        Tc = DyckWord(path).to_ordered_tree().left_right_symmetry()
        Tc = Tc.canonical_labelling().left_right_symmetry()
        
        # extract marks from steep, 2 means marked north step
        marks = [True]
        for i in range(1, len(steep)):
            if steep[i] != 0:
                marks.append(0 != steep[i-1])
        marked = list(path)
        curptr = 0
        for i in range(len(marked)):
            if marked[i] != 0:
                marked[i] = 2 if marks[curptr] else 1
                curptr += 1
        
        # coloring
        colorlist = [-1 for i in range(n+2)]
        colorstack = [-1]
        colorptr = 0
        curcolor = -1
        curlabel = 0
        colorlast = {}
        colorcount = {}
        labellist = [x.label() for x in Tc.pre_order_traversal_iter()]
        for x in marked:
            if 2 == x:
                curcolor += 1
                colorptr += 1
                colorstack.insert(colorptr,curcolor)
                curlabel += 1
                colorlist[curlabel] = curcolor
                colorlast[curcolor] = labellist[curlabel]
                colorcount[curcolor] = 1
            elif 1 == x:
                colorptr += 1
                curlabel += 1
                mycolor = colorstack[colorptr]
                colorlist[curlabel] = mycolor
                colorlast[mycolor] = labellist[curlabel]
                colorcount[mycolor] += 1
            else:
                colorptr -= 1
        
        alpha = sorted(colorlast.items(), key = lambda x: x[1])
        alpha = map(lambda x: colorcount[x[0]], alpha)
        return LACTree(Tc.shape().left_right_symmetry(), alpha)
    
    r"""
    Returns a steep pair in bijection with the LAC-tree
    
    OUTPUT:
    
    A pair ``(steep, path)``, where ``steep`` is a steep path in 0,1 format,
    and ``path`` a Dyck path in 0,1 format.
    """
    def to_steep_pair(self):
        mirtree = self.tree.left_right_symmetry()
        path = mirtree.to_dyck_word()
        colorseen = {}
        steep = []
        for x in mirtree.pre_order_traversal_iter():
            mycolor = self.color[x.label()]
            if mycolor in colorseen:
                steep += [0,1]
            else:
                steep += [1]
                colorseen[mycolor] = 1
        steep += [0] * len(self.alpha)
        steep = steep[1:]
        return (steep, list(path))
        
    r"""
    Returns an LAC-tree in bijection with the given (alpha,231)-avoiding 
    permutation. Do not provide any check (yet).
    
    INPUT:
    
    - ``perm``: a supposedly (alpha,231)-avoiding permutation
    - ``alpha``: a composition indicating the parabolic quotient
    
    OUTPUT:
    
    An LAC-tree in bijection with this (alpha,231)-avoiding permutation
    """
    @staticmethod
    def from_permutation(perm, alpha):
        BT = Permutation(perm).binary_search_tree()
        T = BT.to_ordered_tree_right_branch()
        return LACTree(T, alpha)
    
    r"""
    Returns an (alpha,231)-avoiding in bijection with the LAC-tree
    
    OUTPUT:
    
    A pair ``(perm, alpha)``, where ``perm`` is an (alpha,231)-avoiding 
    permutation, and ``alpha`` a composition indicating the parabolic quotient
    """
    def to_permutation(self):
        n = sum(self.alpha)
        l = len(self.alpha)
        labels = {}
        accu = 1
        for x in self.tree.post_order_traversal_iter():
            if 1 != x.label():
                labels[x.label()] = accu
                accu += 1
        regions = [[] for i in range(l)]
        for i in range(2, n+2):
            regions[self.color[i]].append(labels[i])
        perm = []
        map(perm.extend, regions)
        return (perm, self.alpha)