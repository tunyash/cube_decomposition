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