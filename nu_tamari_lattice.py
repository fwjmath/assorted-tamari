# -*- coding: utf-8 -*-

r"""
`\\nu`-Tamari lattices

This module implements `\\nu`-Tamari lattices, which are lattices on directed
paths indexed by an arbitrary directed path `\\nu`. They were introduced under 
the name of _generalized Tamari lattice_ in [PRV2017]_, in which it was proved
that these lattices are isomorphic to certain intervals in the Tamari lattice.
While it is possible to extract the poset structure directly from
:meth:`TamariLattice`, a more efficient implementation is provided here.

REFERENCES:

.. [PRV2017] Louis-François Préville-Ratelle and Xavier Viennot.
   *The enumeration of generalize Tamari intervals*
   Transactions of the American Mathematical Society. (2017). :arxiv:`1406.3787`.
   
"""

# ****************************************************************************
#       Copyright (C) 2019 Wenjie Fang <fwjmath@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# ****************************************************************************

from sage.combinat.posets.lattices import LatticePoset

def checkpath(p):
    r"""
    This function checks whether p corresponds to a directed lattice path,
    i.e., consists of only 0 and 1.
    
    INPUT:
    
    - ``p`` -- a list of integers
    
    OUTPUT: 
    
    Nothing, but throws an error when ``p`` has elements other than 0 and 1.
    """
    if len(p) != p.count(0) + p.count(1):
        raise ValueError("The input must be a list of 0 (east steps) and 1 (north step).")
    return

def get_level_list(v):
    r"""
    This function returns the level list of the lattice path ``v``.
    
    INPUT:
    
    - ``v`` -- a list of integers standing for a directed lattice path
    
    OUTPUT: 
    
    An array ``lvl`` such that ``lvl[i]`` is the largest abscissa of ordinate 
    ``i``
    """
    p,q = v.count(0), v.count(1)
    lvl = [0 for i in range(q+1)]
    tmp = 0
    ltmp = 0
    for i in v:
        if i == 0: 
            tmp+=1
        else:
            lvl[ltmp] = tmp
            ltmp += 1
    lvl[q] = p
    return lvl

def NuTamariLattice(v):
    r"""
    This function returns the `\\nu`-Tamari lattice indexed by ``v``
    
    INPUT:
    
    - ``v`` -- directed path (canopy) as a list of 0 (east step) and 1 
      (north step)
      
    OUTPUT: the `\\nu`-Tamari lattice indexed by ``v``
    """
        
    def extend_path(elem, cur, toextend, x, y):
        """
        Extending the path (cur) step by step, within the limit of v 
        indicated by lvl.
        
        The parameter (toextend) is the remaining steps to add.
        
        When a path is fully generated, it gets added to (elem).
        """
        if toextend == 0:
            elem.append(tuple(cur))
            return
        if y < (len(lvl) - 1):
            cur.append(1)
            extend_path(elem, cur, toextend - 1, x, y + 1)
            cur.pop()
        if x < lvl[y]:
            cur.append(0)
            extend_path(elem, cur, toextend - 1, x + 1, y)
            cur.pop()
        return
        
    def generate_elements():
        elem = []
        extend_path(elem, [], len(v), 0, 0)
        return elem
        
    def swap(e, p):
        """
        Given a valley p, this function does the v-Tamari switch to obtain a 
        covering element.
        """
        x = [e[:p+1].count(0), e[:p+1].count(1)]
        hdist = lvl[x[1]] - x[0]
        for j in range(p+1, len(e)):
            x[e[j]] += 1
            if hdist == (lvl[x[1]] - x[0]): 
                break
        e1 = list(e)
        for i in range(p,j):
            e1[i] = e1[i+1]
        e1[j] = 0
        return tuple(e1)
            
    def get_cover_elem(e):
        return [swap(e,x) for x in range(len(v)-1) if (e[x] == 0) and (e[x+1] == 1)]
            
    checkpath(v)
    lvl = get_level_list()
    return LatticePoset(dict((e, get_cover_elem(e)) for e in generate_elements()))

def pathpair_to_dyck(u, v):
    r"""
    This function converts an pair of lattice paths ``u`` and ``v`` starting
    and ending at the same point, regarded as an element in Tam(v), into a Dyck
    path that is the corresponding element in the classical Tamari lattice.
    
    INPUT:
    
    - ``u``
    """
    
    # Check basic requirements
    checkpath(u)
    checkpath(v)
    if len(u) != len(v):
        raise ValueError("The two paths should have the same length.")
    if u.count(0) != v.count(1):
        raise ValueError("The two paths should end at the same point.")
    
    ulvl = get_level_list(u)
    vlvl = get_level_list(v)
    h = len(ulvl)
    
    # Check whether u is weakly above v
    for i in range(h):
        if ulvl[i] > vlvl[i]:
            raise ValueError("The path u should be weakly above the path v.")
    
    # The bijection: type given by v, and descent lengths given by consecuted
    # east steps in u
    n = len(u)
    p = []
    ptr = 0
    prev = 0
    for i in range(n):
        p.append(1)
        if v[i] == 1:
            p += [0] * (ulvl[ptr] - prev + 1)
            prev = ulvl[ptr]
            ptr += 1
    p.append(1)
    p += [0] * (ulvl[ptr] - prev + 1)
    return p
