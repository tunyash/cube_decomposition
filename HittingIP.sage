import itertools

class HittingIP:
    def __init__(self, n, max_weight = None, ub = None, codim = None, solver = 'GLPK', lp = False):
        self.n = n
        if max_weight is None:
            max_weight = n
        self.points = [''.join(x) for x in itertools.product('01', repeat=self.n)]
        self.subcubes = [''.join(x) for x in itertools.product('01*', repeat=self.n)]
        self.subcubes = [x for x in self.subcubes if len([c for c in x if c == '1']) <= max_weight]
        if codim is not None:
            self.subcubes = [x for x in self.subcubes if len([c for c in x if c != '*']) == codim]
        self.mip = MixedIntegerLinearProgram(maximization=False, solver=solver)
        if lp:
            self.c = self.mip.new_variable(nonnegative=True, real=True)
        else:
            self.c = self.mip.new_variable(nonnegative=True, integer=True)
        for s in self.subcubes:
            self.mip.set_max(self.c[s], 1)
        self.mip.set_objective(sum(self.c[s] for s in self.subcubes))
        if ub is not None:
            self.mip.add_constraint(sum(self.c[s] for s in self.subcubes) <= ub)
        for pt in self.points:
            sc = [s for s in self.subcubes if all(c == d or c == '*' for (c,d) in zip(s,pt))]
            self.mip.add_constraint(sum(self.c[s] for s in sc) == 1, name = f'cover {pt}')
        for i in range(self.n):
            self.mip.add_constraint(sum(self.c[s] for s in self.subcubes if s[i] != '*') >= 1, name = f'mention {i}')
        for t in itertools.product('01*', repeat=self.n):
            t = ''.join(t)
            if not '*' in t:
                continue
            if t == '*' * self.n:
                continue
            sc = [s for s in self.subcubes if \
                not any((c == '0' and d == '1') or (c == '1' and d == '0') for (c,d) in zip(s,t))]
            sc = [s for s in sc if any(c == '*' and d != '*' for (c,d) in zip(s,t))]
            if t in self.subcubes:
                sc.append(t)
            self.mip.add_constraint(sum(self.c[s] for s in sc) >= 1, name = f'escape {t}')
        try:
            self.value = self.mip.solve()
            self.sol = self.mip.get_values(self.c)
            if lp == False:
                self.sol = Hitting([k for (k,v) in self.sol.items() if v == 1])
                self.value = len(self.sol)
        except sage.numerical.mip.MIPSolverException as e:
            self.error = e
            self.value = None
            self.sol = None

class HC_decomp:
    def __init__(self, n, solver='GLPK', lp=False):
        self.n = n
        self.vertices = [''.join(s) for s in itertools.product('01', repeat=n)]
        self.edges_dict = dict([((v, v[:i] + '1' + v[i+1:]), v[:i] + '*' + v[i+1:]) \
            for v in self.vertices for i in range(n) if v[i] == '0'])
        self.edges = self.edges_dict.keys()
        self.mip = MixedIntegerLinearProgram(maximization=True, solver=solver)
        if lp:
            self.v = self.mip.new_variable(nonnegative=True, real=True)
            self.e = self.mip.new_variable(nonnegative=True, real=True)
        else:
            self.v = self.mip.new_variable(nonnegative=True, integer=True)
            self.e = self.mip.new_variable(nonnegative=True, integer=True)
        self.mip.set_objective(sum(self.v[s] for s in self.vertices))
        for s in self.vertices:
            ee  = [(s, s[:i] + '1' + s[i+1:]) for i in range(n) if s[i] == '0']
            ee += [(s[:i] + '0' + s[i+1:], s) for i in range(n) if s[i] == '1']
            self.mip.add_constraint(self.v[s] + sum(self.e[st] for st in ee) == 1)
        for (s,t) in self.edges:
            self.mip.add_constraint(self.v[s] + self.v[t] <= 1)
        try:
            self.value = self.mip.solve()
            self.sol_v = self.mip.get_values(self.v)
            self.sol_e = self.mip.get_values(self.e)
            if not lp:
                self.v_list = [v for v in self.vertices if self.sol_v[v] == 1]
                self.e_list = [self.edges_dict[e] for e in self.edges if self.sol_e[e] == 1]
                self.sol = Hitting(self.v_list + self.e_list)
        except sage.numerical.mip.MIPSolverException as e:
            self.error = e
            self.value = None

def Forcade(n):
    assert(n % 6 == 0)
    HC = graphs.CubeGraph(n)
    levels = [[v for v in HC.vertices() if sum(c=='1' for c in v)==l] for l in range(n+1)]
    C = [[], [], []]
    for l in range(n/2+1):
        C[l%3].extend(levels[l])
    for l in range(n/2+1, n+1):
        C[(n-l)%3].extend(levels[l])
    C12 = BipartiteGraph(HC.subgraph(C[1] + C[2]))
    M1 = C12.matching()
    D = [[v for v in C[k] if all(v != s and v != t for (s,t,_) in M1)] for k in range(3)]
    D20 = BipartiteGraph(HC.subgraph(D[2] + D[0]))
    M2 = D20.matching()
    E = [[v for v in D[k] if all(v != s and v != t for (s,t,_) in M2)] for k in range(3)]
    points = E[0] + E[1] + E[2]
    edges = [joins(s,t) for (s,t,_) in M1 + M2]
    return Hitting(points + edges)