#!/usr/bin/env sage

from itertools import product as it_product

from copy import deepcopy
from sage.all import *

dim = 5
spaces = [
    [[1, 1, 1, 0, 0, 1], [1, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1]],
    [[1, 1, 0, 0, 0, 1], [1, 1, 1, 1, 0, 0], [1, 0, 1, 0, 1, 1]],
    [[1, 0, 1, 0, 0, 1], [1, 1, 0, 1, 0, 0], [1, 1, 1, 0, 1, 0]],
    [[1, 0, 0, 0, 0, 1], [1, 0, 1, 1, 0, 1], [1, 0, 0, 0, 1, 0]],
    [[0, 1, 1, 0, 0, 1], [0, 1, 1, 1, 0, 0], [1, 1, 0, 0, 1, 1]],
    [[0, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 0]],
    [[0, 0, 1, 0, 0, 1], [1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 1]],
    [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]]
]

def linearize(space):
    s = deepcopy(space)
    for u in s:
        u[-1] = 0
    return s

def is_point_inside(point, space):
    for eq in space:
        if sum(x * y for x, y in zip(point, eq[:-1])) % 2 != eq[-1]:
            return False
    return True

def get_basis(space):
    lin_space = linearize(space)
    m_cont = []
    pr_rank = 0
    for cand in it_product([0,1], repeat=dim):
        if is_point_inside(cand, lin_space):
            t = matrix(GF(2), m_cont + [list(cand)])
            if rank(t) > pr_rank:
                m_cont.append(cand)
                pr_rank = rank(t)
    return m_cont

for space in spaces:
    print(space)
    print('->', get_basis(space))
    for cand in it_product([0,1], repeat=dim):
        if is_point_inside(cand, space):
            print(cand)
            break
