#!/usr/bin/env sage

from sage.all import *
from typing import Tuple, List, Union
from itertools import product, combinations

def affspace_from_string(s: str) -> Tuple[vector, matrix]:
    n = len(s)
    point = vector(GF(2), [1 if x == '1' else 0 for x in s])
    entries = {x:1 for x in enumerate(i for i, x in enumerate(s) if x == '*')}
    space = matrix(GF(2), sum(1 if x == '*' else 0 for x in s), n, entries, sparse=False)
    return point, space

def unite_two_affspaces(a: Tuple[vector, matrix], b: Tuple[vector, matrix]) -> Tuple[vector, matrix]:
    pa, pb = a[0], b[0]
    ma, mb = a[1], b[1]
    linspace = span(ma.rows() + mb.rows() + [pb - pa], GF(2))
    return pa, matrix(GF(2), linspace.basis(), sparse=False)

def within(a: Tuple[vector, matrix], b: Tuple[vector, matrix]) -> bool:
    pa, pb = a[0], b[0]
    ma, mb = a[1], b[1]
    return rank(mb.stack(pa-pb)) == rank(mb) and rank(mb.stack(ma)) == rank(mb)

def intersects(a: Tuple[vector, matrix], b: Tuple[vector, matrix]) -> bool:
    pa, pb = a[0], b[0]
    ma, mb = a[1], b[1]
    try:
        ma.stack(mb).solve_left((pa + pb))
    except ValueError as e:
        return False
    return True

def is_hitting(cubes: List[Tuple[vector, matrix]]) -> bool:
    for cube1, cube2 in combinations(cubes, 2):
        if intersects(cube1, cube2):
            return False
    n = len(cubes[0][0])
    covered = sum(2**rank(cube) for _, cube in cubes)
    return 2**n == covered

def is_reducible(cubes: List[Tuple[vector, matrix]]) -> Tuple[bool, Union[None, Tuple[vector, matrix]]]:
    for cube1, cube2 in combinations(cubes, 2):
        cur = unite_two_affspaces(cube1, cube2)
        while True:
            increment = False
            for cube in cubes:
                if intersects(cube, cur) and not within(cube, cur):
                    cur = unite_two_affspaces(cur, cube)
                    increment = True
            if not increment:
                break
        if cur[1].rank() < cur[1].ncols():
            return True, cur
    return False, None


### Tests ###########################################################
A,B = affspace_from_string('*110'), affspace_from_string('**11')
C = unite_two_affspaces(A, B)
D = affspace_from_string('*111')
E = affspace_from_string('1*11')
assert within(A, C)
assert within(B, C)
assert not within(A, B)
assert not within(C, A)
assert not intersects(A, B) # False
assert intersects(A, C) # True
assert intersects(D, E) # True
assert intersects(D, B) # True
assert not intersects(A, D) # False
#####################################################################

m = int(input())
masks = []
for i in range(m):
    masks.append(input())

lin_masks = [affspace_from_string(mask) for mask in masks]
hitting = is_hitting(lin_masks)
print("Hitting" if hitting else "Not hitting")
if hitting:
    reducible, witness = is_reducible(lin_masks)
    if reducible:
        print('Reducible: ', witness)
    else:
        print('Irreducible')