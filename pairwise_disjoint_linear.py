from itertools import product, combinations
from copy import deepcopy

dim = 5
# spaces = [[[1, 1, 1, 0, 0, 1], [1, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1]],
#             [[1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 1]],
#             [[1, 0, 1, 0, 0, 1], [0, 1, 1, 1, 0, 1], [1, 0, 0, 0, 1, 1]],
#             [[0, 1, 1, 0, 0, 1], [0, 0, 0, 1, 0, 1], [0, 1, 1, 0, 1, 1]],
#             [[0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 1]],
#             [[0, 0, 1, 0, 0, 1], [1, 1, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1]],
#             [[1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1]],
#             [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]]]

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

def disjoint(space1, space2):
    return not any(is_point_inside(point, space1) 
                   and is_point_inside(point, space2) for point in product([0,1], repeat=dim) if sum(point) != 0)


for space1, space2 in combinations(spaces, 2):
    if not disjoint(linearize(space1), linearize(space2)):
        print("NOT DISJOINT")
        print(space1)
        print(space2)


