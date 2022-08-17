#!/usr/bin/env sage

from itertools import product, combinations
import networkx as nx
from copy import deepcopy
nodes = []
codim = 3
dim = codim * 2 - 1

def is_point_inside(point, space):
    for eq in space:
        if sum(x * y for x, y in zip(point, eq[:-1])) % 2 != eq[-1]:
            return False
    return True


def linearize(space):
    s = deepcopy(space)
    for u in s:
        u[-1] = 0
    return s

def disjoint(space1, space2):
    return not any(is_point_inside(point, space1) 
                   and is_point_inside(point, space2) for point in product([0,1], repeat=dim) if sum(point) != 0)



nodes.append([[1 if j == i else 0 for j in range(dim)] + [0] for i in range(codim)])
for z in product([0,1], repeat=codim):
    t = list(z)
    if sum(t) == 0:
        continue
    eq0 = t + [0]*(dim - codim) + [1]
    for x in product(product([0,1], repeat=codim), repeat=codim - 1):
        for a in product([0,1], repeat=codim-1):
            r = [eq0]
            for i in range(codim - 1):
                r.append(list(x[i]) + [1 if j == i else 0 for j in range(codim-1)] + [a[i]])
            nodes.append(r)

print('Nodes count:', len(nodes))

G = nx.Graph()
for nid, _ in enumerate(nodes):
    G.add_node(nid, weight=1)

for (u, value_u), (v, value_v) in combinations(enumerate(nodes), 2):
    if value_u[0] == value_v[0]:
        continue
    intersect = False
    for point in product([0,1], repeat=dim):
        if is_point_inside(point, value_u) and is_point_inside(point, value_v):
            intersect = True
            break
    if not intersect and disjoint(linearize(value_u), linearize(value_v)):
        G.add_edge(u, v)

print('Graph is constructed')

cl_nodes, weight = nx.algorithms.clique.max_weight_clique(G)
for node in cl_nodes:
    print(nodes[node])