#!/usr/bin/env sage


from sage.all import *
from sage.numerical.mip import *
from scipy.optimize import linprog
from itertools import product, combinations

n = 6
prev_bound = 9
vars = list("".join(t) for t in product(['0','1','*'], repeat=n))
print(vars)
id_by_var = dict()
for i, var in enumerate(vars):
    id_by_var[var] = i

matrix = []
rhs = []
# ***
eq = []
for i, var in enumerate(vars):
    eq.append(1 if var == "*"*n else 0)
matrix.append(eq)
rhs.append(0)

for k in range(1, n + 1):
    for var_set, values in product(combinations(range(n), k), product(['0', '1'], repeat=k)):
        eq = []
        for i, var in enumerate(vars):
            matches = all(var[j] != val for j, val in zip(var_set, values)) and \
                      any(var[j] != '*' for j in var_set)
            eq.append(1 if matches else 0)
        print(var_set, values, '->', eq)
        matrix.append(eq)
        rhs.append(2)

for excluded in range(n):
    eq = []
    for i, var in enumerate(vars):
        matches = any(val != '*' and j != excluded for j, val in enumerate(var))
        eq.append(1 if matches else 0)
    matrix.append(eq)
    rhs.append(prev_bound)

#neg_matrix = [[-v for v in u] for u in matrix]
#neg_rhs = [-v for v in rhs]

#solution = linprog([1]*len(vars), A_ub=neg_matrix, b_ub=neg_rhs, method='highs', integrality=[1]*len(vars))

p = MixedIntegerLinearProgram()
taken = p.new_variable(binary=True)
p.set_objective(p.sum(-taken[i] for i in vars))
for row, rhs_val in zip(matrix, rhs):
    p.add_constraint(p.sum(row[i] * taken[var] for i, var in enumerate(vars)) >= rhs_val)
print(p.show())
print(p.solve())
