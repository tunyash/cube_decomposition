import json

def disjoint(s,t):
    "determine whether two subcubes are disjoint"
    return any(set([c,d]) == set(['0','1']) for (c,d) in zip(s,t))

def joinc(c,d):
    "compute the join of two symbols in {0,1,*}"
    if c == '*': return '*'
    if d == '*': return '*'
    if c == d: return c
    return '*'

def joins(s,t):
    "compute the join of two subcubes"
    return ''.join(joinc(c,d) for (c,d) in zip(s,t))

def escapes(s,t):
    "determine whether s escapes t"
    return not disjoint(s,t) and any(c == '*' and d != '*' for (c,d) in zip(s,t))

def nstars(s):
    "compute the dimension of given subcube"
    return len([c for c in s if c == '*'])

class HittingMixin:
    def is_tight(self):
        "determine whether given formula is tight (mentions all variables)"
        return self.dim() == self.n

    def is_homogeneous(self):
        "determine whether formula is homogeneous"
        dims = self.dimensions()
        return all(x == dims[0] for x in dims)

    def __len__(self):
        "return number of clauses"
        return len(self.F)

    def properties(self):
        "return several properties of self"
        def histogram(data):
            D = {}
            for x in data:
                if x not in D:
                    D[x] = 0
                D[x] += 1
            return sorted(D.items(), key = lambda kv: kv[0], reverse = True)
        res = {}
        res['variables'] = self.n
        res['clauses'] = self.m
        res['dim'] = self.dim()
        res['dimensions'] = histogram(self.dimensions())
        res['hitting'] = self.is_hitting()
        res['tight'] = self.is_tight()
        res['irreducible'] = self.is_irreducible()
        res['homogeneous'] = self.is_homogeneous()
        return res

class Hitting(HittingMixin):
    def __init__(self, F, suppress_check = False):
        "init class with a list of strings over 0/1/*"
        self.F = F
        n = self.n = len(F[0])
        m = self.m = len(F)
        assert(all(all(c in '01*' for c in x) for x in F))
        if not suppress_check:
            assert(self.is_hitting() == True)

    def __repr__(self):
        return f'Hitting({repr(self.F)})'

    def dimensions(self):
        return [nstars(x) for x in self.F]

    def is_hitting(self):
        "determine whether given formula is hitting"
        n, m, A = self.n, self.m, self.F
        if any(not disjoint(A[i],A[j]) for i in range(m) for j in range(i)):
            return [(A[i],A[j]) for i in range(m) for j in range(i) if not disjoint(A[i],A[j])]
        return sum(2^nstars(s) for s in A) == 2^n

    def is_irreducible(self, witness = False):
        "determine whether given formula is irreducible"
        n, m, A = self.n, self.m, self.F
        for i in range(m):
            for j in range(i):
                s = joins(A[i],A[j])
                changed = True
                while changed:
                    changed = False
                    for t in A:
                        if escapes(t,s):
                            s = joins(t,s)
                            changed = True
                if s != '*' * n: return s if witness else False
        return True

    def reducibility_index_serial(self, by_pair = False):
        "return maximum number of joins in serial implementation"
        n, m, A = self.n, self.m, self.F
        pairs = dict()
        max_iter = 0
        for i in range(m):
            for j in range(i):
                s = joins(A[i],A[j])
                changed = True
                iter = 0
                while changed:
                    changed = False
                    for t in A:
                        if escapes(t,s):
                            s = joins(t,s)
                            iter += 1
                            changed = True
                pairs[(i,j)] = iter
                max_iter = max(iter, max_iter)
        return (max_iter, pairs) if by_pair else max_iter

    def reducibility_index_parallel(self, by_pair = False):
        "return maximum number of eventful loop iterations in parallel implementation"
        n, m, A = self.n, self.m, self.F
        max_iter = 0
        pairs = dict()
        for i in range(m):
            for j in range(i):
                s = joins(A[i],A[j])
                iter = -1
                while True:
                    iter += 1
                    r = s
                    for t in A:
                        if escapes(t,s):
                            r = joins(t,r)
                    if r == s:
                        break
                    s = r
                pairs[(i,j)] = iter
                max_iter = max(iter, max_iter)
        return (max_iter, pairs) if by_pair else max_iter

    def dim(self):
        "return effective dimension"
        return sum(any(x[i] != '*' for x in self.F) for i in range(self.n))

    def subcube_to_subspace(self, subcube):
        "convert a subcube to a subspace"
        V = VectorSpace(GF(2), self.n + 1)
        S = [[1] + [int(c == '1') for c in subcube]]
        for (i,c) in enumerate(subcube):
            if c == '*':
                S += [[0] + [0] * i + [1] + [0] * (self.n - i - 1)]
        return V.subspace(map(V, S))

    def to_plus(self):
        "construct an equivalent HittingPlus instance"
        return HittingPlus([self.subcube_to_subspace(x) for x in self.F])

    def by_star_pattern(self):
        "partition subcubes according to star pattern"
        trans = {'0': 'b', '1': 'b', '*': '*'}
        patterns = {}
        for x in self.F:
            pattern = ''.join(trans[c] for c in x)
            if pattern not in patterns:
                patterns[pattern] = []
            patterns[pattern].append(x)
        return patterns

    def to_plus_compressed(self):
        "construct an equivalent HittingPlus instance, compressing pairs of subcubes with the same star pattern"
        patterns = self.by_star_pattern()
        return HittingPlus([sum((self.subcube_to_subspace(S) for S in val), 0) for val in patterns.values()])

    def split(self, i):
        "recursive construction which splits on the i'th coordinate"
        def split_line(x, i):
            y, b, z = x[:i], x[i], x[i+1:]
            if b == '*':
                return [y + '**' + z + '*']
            else:
                return [y + b + '*' + z + '0', y + '*' + b + z + '1']
        return Hitting(sum((split_line(x,i) for x in self.F), []))

    def split_all(self):
        "apply split on all coordinates"
        H = self
        for i in range(self.n):
            H = H.split(2*i)
        return H

    def merge(self, other):
        "merge formula with other formula"
        F0 = ['0' + x for x in self.F if x not in other.F]
        F1 = ['1' + x for x in other.F if x not in self.F]
        Fs = ['*' + x for x in self.F if x in other.F]
        return Hitting(F0 + F1 + Fs)

    def x(self, i):
        assert(0 <= i < self.n)
        return self.vars[i]

    def y(self, i, j):
        assert(0 <= i < self.n)
        assert(0 <= j <= self.m)
        return self.vars[self.n + (self.m+1) * i + j]

    def ExtPC_init(self, fld = GF(2)):
        "initialize ExtPC proof over given field"
        def to_poly(i, c):
            if c == '*':
                return 1
            elif c == '0':
                return 1 - self.x(i)
            else:
                return self.x(i)
        xs = [f'x{i}' for i in range(self.n)]
        ys = [f'y{i}_{j}' for i in range(self.n) for j in range(self.m+1)]
        self.R = fld[','.join(xs + ys)]
        self.vars = self.R.gens()
        init = [[to_poly(i, C[i]) for i in range(self.n)] for C in self.F]
        init += [[-1] + [1] * (self.n-1)]
        self.proof = [init]
        self.next_q = 0
        self.defs = dict((self.x(i), self.x(i)) for i in range(self.n))

    def ExtPC_merge(self, p1, p2):
        "merge positions p1 < p2, use position p1 for results"
        q = self.next_q
        self.next_q += 1
        assert(0 <= p1 < p2 < len(self.proof[-1]))
        assert(0 <= q < self.n)
        last = self.proof[-1]
        s = Sequence([P[p1] * P[p2] for P in last])
        C, mon = s.coefficient_matrix()
        rs = C.row_space()
        L = [rs.echelon_coordinates(row) for row in C.rows()]
        L = [sum(cf * self.y(q,j) for (j,cf) in enumerate(row)) for row in L]
        self.proof.append([r[:p1] + [s] + r[p1+1:p2] + r[p2+1:] for (r,s) in zip(last, L)])
        basis = rs.basis_matrix() * mon
        for (j,b) in enumerate(basis):
            self.defs[self.y(q,j)] = b[0]

    def ExtPC_done(self):
        "check that we have reached the final step"
        return len(self.proof[-1][0]) == 1

    def ExtPC_zero_sum(self):
        "check that the sum is zero at the final step"
        assert(self.ExtPC_done())
        return sum(r[0] for r in self.proof[-1]) == 0

    def ExtPC_check(self, fld = GF(2), strategy = 'serial'):
        "check that ExtPC proof works over given field and using given strategy (serial or parallel)"
        self.ExtPC_init(fld)
        if strategy == 'serial':
            for _  in range(self.n-1):
                self.ExtPC_merge(0, 1)
        elif strategy == 'parallel':
            N = self.n
            while N > 1:
                for i in range(N // 2):
                    self.ExtPC_merge(i, i+1)
                N = (N+1)//2
        else:
            return None
        return self.ExtPC_zero_sum() and self.ExtPC_check_final_expr()

    def elaborate(self, P):
        "convert any expression over the x and y to an expression over the x"
        prev = None
        while prev != P:
            prev = P
            P = P.subs(self.defs)
        return P

    def ExtPC_check_final_expr(self):
        "check that final expressions represent initial clauses"
        assert(self.ExtPC_done())
        return all(self.elaborate(P[0]) == product(Q) \
            for (P,Q) in zip(self.proof[-1], self.proof[0]))

class HittingPlus(HittingMixin):
    def __init__(self, F, suppress_check = False):
        "init class with a collection of subspaces of VectorSpace(GF(2),n+1) representing the projective closure"
        self.F = F
        self.V = F[0].ambient_vector_space()
        self.n = self.V.dimension() - 1
        self.m = len(F)
        self.O = self.V.subspace([self.V([int(i==j) for j in range(self.n+1)])\
             for i in range(1, self.n+1)]) # O = 0*^n
        if not suppress_check:
            assert(self.is_hitting() == True)

    def __repr__(self):
        return f'HittingPlus({repr(self.F)})'

    def dimensions(self):
        return [x.dimension() for x in self.F]

    def is_hitting(self):
        "determine whether formula is hitting"
        # each subspace intersects 1*^n
        if any(S <= self.O for S in self.F):
            return False
        # the intersection of any two subspaces with 1*^n is empty
        if not all(self.F[i].intersection(self.F[j]) <= self.O \
                for i in range(1, self.m) for j in range(i)):
            return False
        # the subspaces cover everything
        return sum(2^S.dimension() for S in self.F) == 2^(self.n + 1)

    def dim(self):
        "return effective dimension"
        I = self.F[0]
        for S in self.F:
            I = I.intersection(S)
        return self. n - I.dimension()

    def is_irreducible(self, witness = False):
        "determine whether formula is irreducible"
        for i in range(self.m):
            for j in range(i):
                s = self.F[i] + self.F[j]
                changed = True
                while changed:
                    changed = False
                    for t in self.F:
                        if not t.intersection(s) <= self.O and \
                            not t <= s:
                            s = t + s
                            changed = True
                if s.dimension() < self.n + 1: return s if witness else False
        return True

def standard(n):
    "standard construction for n >= 3"
    assert(n >= 3)
    F  = ['1'*i + '000' + '*' * (n-3-i) for i in range(n-2)]
    F += ['01' + '*' * (n-2)]
    F += ['1'*i + '*01' + '*' * (n-3-i) for i in range(n-2)]
    F += ['1' * (n-2) + '*0']
    F += ['1' * n]
    return Hitting(F)

def standard_linear(n):
    "standard construction for n >= 3, joining the two points"
    H = standard(n).to_plus()
    return HittingPlus([H.F[0] + H.F[-1]] + H.F[1:-1])

def homogeneous4():
    "homogeneous construction for n = 4"
    return Hitting(['001*', '0*01', '01*0', '110*', '1*10', '10*1', '*000', '*111'])

def special6():
    "construction with many stars for n = 6"
    F  = ['0*0*1*', '1**0*1', '00**0*', '10***0']
    F += ['001*1*', '10*1*1', '010*0*', '11*0*0']
    F += ['*111**', '0110**', '1101**']
    return Hitting([reversed(x) for x in F])

def standard_stars(n):
    "construction with many stars for arbitrary n"
    assert(n >= 3)
    if is_odd(n):
        F = standard(3)
        while n > 3:
            F = F.split(0)
            n -= 2
        return F
    else:
        if n == 4:
            return standard(4)
        else:
            F = standard(6)
            while n > 6:
                F = F.split(0)
                n -= 2
            return F

def standard_homogeneous(t):
    "homogeneous construct with t iterations"
    F = homogeneous4()
    for _ in range(t):
        F = F.split_all()
    return F

def standard_points(n):
    "construction with many points"
    N = { '0': '1', '1': '0', '*': '*' }
    F = standard(3)
    while n > 3:
        n -= 1
        G = Hitting([N[x[0]] + x[1:] for x in F.F])
        F = F.merge(G)
    return F

def special7_linear():
    "irreducible hitting(+) formula for n = 5 with 7 subspaces"
    H = Hitting(['00***', '1001*', '1*00*', '0100*', '1*1*0',\
         '*1*11', '101*1', '*1101', '011*0', '*1010'])
    F = H.to_plus().F
    return HittingPlus([F[0], F[1]+F[3], F[2], F[4], F[5], F[6]+F[8], F[7]+F[9]])

def cubic(n):
    "irreducible hitting formula (cubic construction)"
    assert(is_odd(n))
    assert(n >= 3)
    m = n // 2
    F  = ['0' * n]
    F += ['*' * i + '0' * m + '1' + '*' * (m - i) for i in range(m+1)]
    F += ['0' * i + '1' + '*' * m + '0' * (m - i) for i in range(m)]
    F += ['0' * i + '1' + '*' * j + '0' * k + '1' + \
        '*' * (m - 1 - j - k) + '0' * j + '1' + '*' * (m - 1 - i - j) \
            for j in range(m) for i in range(m-j) for k in range(m-j)]
    return Hitting(F)

def cubic_linear(n):
    "linear version of cubic()"
    F = cubic(n)
    i = [j for (j,x) in enumerate(F.F) if nstars(x) == 0][1]
    H = F.to_plus()
    return HittingPlus([H.F[0] + H.F[i]] + H.F[1:i] + H.F[i+1:])

def desarguesian_spread(t):
    "irreducible hitting(+) formula based on the standard Desarguesian spread"
    V = VectorSpace(GF(2), 2*t)
    F = GF(2^t)
    z = F.gen()
    def base_reduction(x):
        L = x.polynomial().list()
        return L + [0] * (t - len(L))
    return HittingPlus([\
        V.subspace(V(base_reduction(z^k) + base_reduction(a * z^k)) for k in range(t))\
        for a in F])

def peitl():
    "return all irreducible hitting formulas of minimal size for n=4,5,6,7"
    return json.loads(open('peitl.json', 'r').read())