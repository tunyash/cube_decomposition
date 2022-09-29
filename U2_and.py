#!/usr/bin/env sage

import sys
from sage.all import *
from itertools import product

import pysat
import pysat.card
import pysat.solvers
from itertools import product, combinations
from typing import Tuple, List, Set
from collections import defaultdict
from scipy.optimize import linprog

def fits(point, mask):
    return all(y == '*' or x == y for x,y in zip(point, mask))

def gen_certs(n: int, k: int, bound: int) -> List[str]:
    certs = []
    for vars in combinations(range(n), k):
        for values in product([0,1], repeat=k):
            if sum(values) == k:
                continue
            mask = ['*']*n
            for i, v in zip(vars, values):
                mask[i] = '0' if v == 0 else '1'
            certs.append("".join(mask))
    return certs

def generate_cnf(n: int, k: int, bound: int):
    id_pool = pysat.formula.IDPool()
    cnf = []
    certs = gen_certs(n, k, bound)
    for point in product([0,1], repeat=n):
        if sum(point) == n or sum(point) > bound:
            continue
        #print(point)
        str_point = "".join('0' if i == 0 else '1' for i in point)
        clause = []
        good_certs = []
        for cert in certs:
            if fits(str_point, cert):
                clause.append(id_pool.id(cert))
                good_certs.append(cert)
        #print(good_certs)
        cnf.append(clause)
        for cert1, cert2, cert3 in combinations(good_certs, 3):
            cnf.append([-id_pool.id(cert1), -id_pool.id(cert2), -id_pool.id(cert3)])
    #print(certs)
    #print(cnf)
    return id_pool, cnf

def solve_linprog(n: int, k: int):
    certs = gen_certs(n, k, k)
    matrix = []
    rhs = []
    for point in product([0,1], repeat=n):
        if sum(point) == n:
            continue  
        str_point = "".join('0' if i == 0 else '1' for i in point)
        row = [1 if fits(str_point, cert) else 0 for cert in certs]
        matrix.append(row)
        rhs.append(2)
        matrix.append([-x for x in row])
        rhs.append(-1)
    matrix.append([1] * len(certs))
    rhs.append(2**(n-k)*2)
    eq = [[1 if cert == '0'*k + '*'*(n-k) else 0 for cert in certs]]
    eq_rhs = [1]
    print(matrix)
    print(rhs)
    return linprog([1]*len(certs), A_ub=matrix, b_ub=rhs, A_eq=eq, b_eq=eq_rhs)
    


def run_satsolver(n: int, k: int, bound: int):
    id_pool, cnf = generate_cnf(n, k, bound)
    solver = pysat.solvers.Solver(name="g4", bootstrap_with=cnf)
    sat = solver.solve(assumptions=[id_pool.id('0'*k + '*'*(n-k))])
    if not sat:
        return None
    model = solver.get_model()
    result = []
    for a in model:
        if a > 0:
            result.append(id_pool.obj(a))
    return result


n, k, bound = 11, 3, 3
result = run_satsolver(n, k, bound)
print(result)
# result = solve_linprog(n, k)

# for i, cert in enumerate(gen_certs(n, k)):
#     print(cert, result.x[i])

# for point in product([0,1], repeat=n):
#     if sum(point) == n:
#          continue  
#     str_point = "".join('0' if i == 0 else '1' for i in point)
#     print(str_point, sum(result.x[i] if fits(str_point, cert) else 0 for i, cert in enumerate(gen_certs(n, k))))
    
