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

def nfs_flip(x, y):
    "return the nfs flip of x and y, or None if they do not form an nfs pair"
    assert(len(x) == len(y))
    assert(all(c in '01*' for c in x+y))
    n = len(x)
    i_s = [i for i in range(n) if x[i] != y[i] and x[i] in '01' and y[i] in '01']
    j_s = [j for j in range(n) if (x[j] == '*' and y[j] in '01') or (x[j] in '01' and y[j] == '*')]
    if len(i_s) != 1 or len(j_s) != 1:
        return None
    i = i_s[0]
    j = j_s[0]
    flip = { '0': '1', '1': '0' }
    if y[j] == '*':
        return x[:i] + '*' + x[i+1:], y[:j] + flip[x[j]] + y[j+1:]
    else:
        return x[:j] + flip[y[j]] + x[j+1:], y[:i] + '*' + y[i+1:]

def is_nfs_pair(x, y):
    "determine whether x, y form an nfs_pair"
    return nfs_flip(x, y) is not None

class HittingMixin:
    def is_tight(self):
        "determine whether given formula is tight (mentions all variables)"
        return self.dim() == self.n

    def is_tight_irreducible(self):
        "determine whether given formula is both tight and irreducible"
        return self.is_tight() and self.is_irreducible()

    def is_homogeneous(self):
        "determine whether formula is homogeneous"
        dims = self.dimensions()
        return all(x == dims[0] for x in dims)

    def __len__(self):
        "return number of clauses"
        return len(self.F)

    def __iter__(self):
        "iterate over clauses"
        return self.F.__iter__()

    # __setitem__ not implemented
    def __getitem__(self, item):
        "get i'th clause"
        assert(0 <= item < self.m)
        return self.F[item]

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

    def __str__(self):
        return '\n'.join(self.F)

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

    def is_regular(self):
        "determine whether formula is regular"
        return all(all(len([x for x in self.F if x[i] == b]) >= 2 for i in range(self.n)) for b in '01')

    def dim(self):
        "return effective dimension"
        return sum(any(x[i] != '*' for x in self.F) for i in range(self.n))

    def weight(self, q0, q1):
        "return number of clauses when substituting q0 for 0 and q1 for 1"
        q = {'0': q0, '1': q1, '*': 1}
        return sum(product(q[c] for c in x) for x in self.F)

    def rotate(self, rot):
        "rotate left by rot"
        if rot == 0:
            return Hitting(self.F)
        if rot < 0:
            rot = self.n - (-rot)
        return Hitting([x[rot:] + x[:rot] for x in self.F])

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
        assert(self.n == other.n)
        F0 = ['0' + x for x in self.F if x not in other.F]
        F1 = ['1' + x for x in other.F if x not in self.F]
        Fs = ['*' + x for x in self.F if x in other.F]
        return Hitting(F0 + F1 + Fs)

    def decompose(self, coord, placeholder = False):
        "decompose along coordinate"
        assert(0 <= coord < self.n)
        ins = '*' if placeholder else ''
        return tuple([Hitting([x[:coord] + ins + x[coord+1:] for x in self.F if x[coord] != val])\
            for val in '10'])

    def irreducible_decompositions(self, one_sided = False):
        "return decompositions which are irreducible"
        L = [(i, self.decompose(i)) for i in range(self.n)]
        if one_sided:
            return [(i,Hs) for (i,Hs) in L if Hs[0].is_irreducible() or Hs[1].is_irreducible()]
        else:        
            return [(i,Hs) for (i,Hs) in L if Hs[0].is_irreducible() and Hs[1].is_irreducible()]

    def nfs_pairs(self):
        "return all pairs of indices of nfs pairs"
        return [(i,j) for j in range(self.m) for i in range(j) if is_nfs_pair(self.F[i], self.F[j])]

    def nfs_flip(self, i, j):
        "flip an nfs pair"
        if i > j:
            i, j = j, i
        assert(0 <= i < j < self.m)
        assert(is_nfs_pair(self.F[i], self.F[j]))
        Gi, Gj = nfs_flip(self.F[i], self.F[j])
        return Hitting(self.F[:i] + [Gi] + self.F[i+1:j] + [Gj] + self.F[j+1:])

    def extend_by_nfs_flip(self, i, j):
        "extend current formula by flipping the pair (i,j)"
        if i > j:
            i, j = j, i
        assert(0 <= i < j < self.m)
        assert(is_nfs_pair(self.F[i], self.F[j]))
        x0, x1 = self.F[i], self.F[j]
        y0, y1 = nfs_flip(x0, x1)
        G = [x + '*' for (k,x) in enumerate(self.F) if k not in [i,j]]
        G += [x0 + '0', x1 + '0', y0 + '1', y1 + '1']
        return Hitting(G)

    def undo_nfs_flip(self, coord, bit = '0'):
        "attempt to undo nfs flip at coord (return None if unsuccessful)"
        assert(0 <= coord < self.n)
        i_s = [i for (i,x) in enumerate(self.F) if x[coord] == '0']
        j_s = [j for (j,x) in enumerate(self.F) if x[coord] == '1']
        if len(i_s) != 2 or len(j_s) != 2:
            return None
        x, y = self.F[i_s[0]], self.F[i_s[1]]
        z, w = self.F[j_s[0]], self.F[j_s[1]]
        x = x[:coord] + x[coord+1:]
        y = y[:coord] + y[coord+1:]
        z = z[:coord] + z[coord+1:]
        w = w[:coord] + w[coord+1:]
        if not is_nfs_pair(x, y):
            return None
        if nfs_flip(x, y) not in [(z, w), (w, z)]:
            return None
        k_s = j_s if bit == '0' else i_s
        return Hitting([x[:coord] + x[coord+1:] for (i,x) in enumerate(self.F) if i not in k_s])
    
    def undo_nfs_flip_all(self, bit = '0', only_irreducible = False):
        "return all ways (if any) to undo nfs flips"
        L = [(i, self.undo_nfs_flip(i, bit)) for i in range(self.n)]
        L = [(i, H) for (i, H) in L if H is not None]
        if only_irreducible:
            L = [(i, H) for (i, H) in L if H.is_irreducible()]
        return L

    def greedy_decision_tree(self, path = None, root = None):
        "construct a greedy decision tree for determining which subcube contains input"
        if path is None:
            path = '*' * self.n
            root = self
        if self.dim() == 0:
            subcubes = [x for x in root.F if all(c == d or d == '*' for (c,d) in zip(path, x))]
            assert(len(subcubes) == 1)
            return {'tree': subcubes[0], 'leaves': 1, 'depth': 0}
        stats = [(i,len([x for x in self.F if x[i] != '*'])) for i in range(self.n)]
        i = max(stats, key=lambda x: x[1])[0]
        H0, H1 = self.decompose(i, True)
        T0 = H0.greedy_decision_tree(path[:i] + '0' + path[i+1:], root)
        T1 = H1.greedy_decision_tree(path[:i] + '1' + path[i+1:], root)
        return {'tree': (i, T0['tree'], T1['tree']),\
            'leaves': T0['leaves'] + T1['leaves'],\
            'depth': max(T0['depth'], T1['depth']) + 1}

    def x(self, i):
        assert(0 <= i < self.n)
        return self.vars[i]

    def y(self, i, j):
        assert(0 <= i < self.n)
        assert(0 <= j <= self.m)
        return self.vars[self.n + (self.m+1) * i + j]

    ### ExtPC proof
    ### run with ExtPC_check() or ExtPC_check(strategy = 'parallel') [different merging strategies]
    ### the proof runs in n-1 steps, in each of which two coordinates are merged
    ### proof[i] is the contents of the i'th step
    ### each item in proof[i] is a representation of one the clauses (first m items) or of -1 (last item)
    ### the items are stored as lists of affine univariate polynomials, whose product is the item
    ### the original variables are x0, ..., x(n-1)
    ### in the i'th step, variables yi_0, ..., yi_(r-1) are used (for some r)
    ### the definitions of the extension variables are in defs
    ### q_list[i] contains the original coordinates represented by yi_j

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
        init += [[fld(-1)] + [fld(1)] * (self.n-1)]
        self.proof = [init]
        self.defs = dict((self.x(i), self.x(i)) for i in range(self.n))
        self.coords = [[i] for i in range(self.n)]
        self.q_list = []

    def ExtPC_merge(self, p1, p2):
        "merge positions p1 < p2, use position p1 for results"
        q = len(self.q_list)
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
        self.coords = self.coords[:p1] + [self.coords[p1] + self.coords[p2]] +\
                self.coords[p1+1:p2] + self.coords[p2+1:]
        self.q_list.append(self.coords[p1])

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
        assert(len(F) > 0)
        if type(F[0]) is type(''):
            self.F = [self.decode(x) for x in F]
        else:
            self.F = F
        self.V = self.F[0].ambient_vector_space()
        self.n = self.V.dimension() - 1
        self.m = len(self.F)
        # self.H is the hyperplane at infinity
        self.O = self.V.subspace([self.V([int(i==j) for j in range(self.n+1)])\
             for i in range(1, self.n+1)]) # O = 0*^n
        if not suppress_check:
            assert(self.is_hitting() == True)

    def __repr__(self):
        return 'HittingPlus([' + ', '.join("'" + self.express(x) + "'" for x in self) + '])'

    def __str__(self):
        return '\n'.join(self.express(x) for x in self)

    def express(self, x):
        "express subspace alphanumerically"
        basis = x.basis()
        assert(basis[0][0] == 1)
        shift = basis[0][1:]
        basis = [y[1:] for y in basis[1:]]
        shift_str = ''.join('01'[c] for c in shift)
        basis_str = [''.join('01'[c] for c in b) for b in basis]
        return shift_str + ' + <' + ', '.join(basis_str) + '>'

    def decode(self, x):
        "decode textual subspace"
        parts = x.split('+')
        assert(len(parts) == 2)
        shift = parts[0].strip()
        basis = parts[1].strip()

        assert(all(c in '01' for c in shift))
        if 'n' not in dir(self):
            self.n = len(shift)
        assert(len(shift) == self.n)
        shift = [int(c) for c in shift]

        assert(basis[0] == '<')
        assert(basis[-1] == '>')
        basis = [b.strip() for b in basis[1:-1].split(',')]
        assert(all(len(b) == self.n for b in basis))
        assert(all(all(c in '01' for c in b) for b in basis))
        basis = [[int(c) for c in b] for b in basis]

        V = VectorSpace(GF(2), self.n + 1)
        return V.subspace([V([1] + shift)] + [V([0] + b) for b in basis])

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

    def uncovered_points(self):
        "return points in O not covered by F"
        return [pt for pt in self.O if not any(pt in V for V in self.F)]

    def uncovered_subspace(self):
        "return subspace generated by uncovered points"
        return self.V.subspace(map(self.V, self.uncovered_points()))

    def all_subspaces(self):
        "return all subspaces (including the one at infinity)"
        return self.F + [self.uncovered_subspace()]

def standard(n):
    "standard construction for n ≥ 3"
    assert(n >= 3)
    F  = ['1'*i + '000' + '*' * (n-3-i) for i in range(n-2)]
    F += ['01' + '*' * (n-2)]
    F += ['1'*i + '*01' + '*' * (n-3-i) for i in range(n-2)]
    F += ['1' * (n-2) + '*0']
    F += ['1' * n]
    return Hitting(F)

def standard_few1(n):
    "construction with few 1's for n ≥ 3"
    assert(n >= 3)
    if n == 3:
        return Hitting(['01*', '110', '1*1', '*00', '001'])
    return Hitting(\
        ['0' * i + '1' + '*' * (n - 1 - i) for i in range(1, n)] +\
        ['100' + '*' * i + '1' + '0' * (n - i - 4) for i in range(n - 4)] +\
        ['110' + '*' * (n - 4) + '0', '1*1' + '*' * (n - 3)] +\
        ['1*0' + '*' * (n - 4) + '1', '*' + '0' * (n - 1)])

def standard_few1_iter(n):
    "variant of standard_few1"
    assert(n >= 3)
    G = Hitting(['1*', '00', '01'])
    F0 = Hitting(['01*', '110', '1*1', '*00', '001'])
    return iteration_merge(F0, G, 1, 1, n - 3)

def standard_linear(n):
    "standard construction for n ≥ 3, joining the two points"
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
    return Hitting(F)
    #return Hitting([x[::-1] for x in F])

def special6a():
    "variant of special6"
    F  = ['000***', '10*0**', '*1**00', '**111*', '*10**1']
    F += ['*0110*', '*1101*', '*11*01', '*10*10', '0010**', '1001**']
    return Hitting(F)

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
            F = special6()
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

def kurz_iterative(H, t):
    "apply the Kurz iteration t times on a hitting formula containing 01*...*"
    for _ in range(t):
        assert('01' + '*' * (H.n-2) in H.F)
        H0 = Hitting(['*' + x for x in H.F])
        H1 = Hitting([x + '*' * (H.n-2) for x in ['000', '111', '01*', '*01', '1*0']])
        H = H0.merge(H1)
        H = Hitting([x[2:4] + x[:2] + x[4:] for x in H.F])
    return H

def kurz_linear(n, subcubes = False):
    "return the Kurz construction"
    assert(n >= 3)
    if is_odd(n):
        #H5 = Hitting(['01***', '110**' ,'*000*', '1*1*0', '*0*11', '111*1', '001*0', '*0101', '*0010'])
        H3 = standard(3)
        H = kurz_iterative(H3, (n-3)//2)
    else:
        H4 = Hitting(['01**', '1*0*', '000*', '1*10', '*011', '0010', '1111'])
        H = kurz_iterative(H4, (n-4)//2)
    return H if subcubes else H.to_plus_compressed()

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

def nfs_iteration(H, iter, i = None, j = None):
    "iterative construction using nfs pairs (default for initial i,j is last two subcubes)"
    if i is None or j is None:
        i, j = H.m - 2, H.m - 1
    for _ in range(iter):
        H = H.extend_by_nfs_flip(i, j)
        i, j = H.m - 2, H.m - 1
    return H

def standard_nfs_iteration(n):
    "irreducible hitting formula formed by nfs iteration"
    assert(n >= 3)
    return nfs_iteration(standard(3), n - 3)

def iterative_construction(G, s, iter, F0 = None):
    "iterative construction with s stars (example: G = standard(3), s = 0 or s = 1)"
    if F0 is None:
        if s > 0:
            F0 = Hitting([x[s:] + x[:s] for x in G])
        else:
            pairs = G.nfs_pairs()
            assert(len(pairs) > 0)
            F0 = G.extend_by_nfs_flip(*pairs[-1])
    assert(s + F0.n >= G.n)
    for _ in range(iter):
        F0 = Hitting(['*' * s + x for x in F0])
        G0 = Hitting([x + '*' * (F0.n - G.n) for x in G])
        F0 = F0.merge(G0)
        F0 = Hitting([x[s+1:] + x[:s+1] for x in F0])
    return F0

def iteration_codim2(F0, iter):
    "iteration on formula containing 01*^{n-2}, such as standard(3); go backward if iter < 0"
    if iter >= 0:
        assert('01' + '*' * (F0.n-2) in F0)
        for _ in range(iter):
            S  = ['1' + x for x in F0 if x != '01' + '*' * (F0.n-2)]
            S += ['01' + '*' * (F0.n-1), '*01' + '*' * (F0.n-2), '000' + '*' * (F0.n-2)]
            F0 = Hitting(S)
        return F0
    else:
        for _ in range(-iter):
            T = ['01' + '*' * (F0.n-2), '*01' + '*' * (F0.n-3), '000' + '*' * (F0.n-3)]
            assert(all(x in F0 for x in T))
            F0 = Hitting([x[1:] for x in F0 if x[0] == '1'] + [T[0][:-1]])
        return F0

def iteration_merge(F, G, b, rot, iter):
    "merge gadget G into F for iter many iterations; put G in position b, and rotate left each time by rot"
    for _ in range(iter):
        G0 = Hitting([x + '*' * (F.n - G.n) for x in G])
        if b == 0:
            F = G0.merge(F)
        else:
            F = F.merge(G0)
        F = F.rotate(rot)
    return F.rotate(-rot)

def best_linear(n):
    "current best construction of hitting(+) formulas for n ≥ 3 (standard(n) is best for hitting)"
    assert(n >= 3)
    if is_odd(n):
        return iterative_construction(standard(3), 1, (n-3)//2).to_plus_compressed()
    elif n == 4:
        return standard(4).to_plus_compressed()
    else:
        return iterative_construction(special6a(), 1, (n-6)//2).to_plus_compressed()

def best_linear_params(max_n):
    "return parameters of best_linear construction"
    return dict([(F.n, len(F)) for F in [best_linear(n) for n in range(3, max_n+1)]\
        if F.is_tight_irreducible()])

def standard_points_exact(n, pts):
    "generate tight irreducible formula with given even number of points between 2 and 2^{n-2}"
    assert(is_even(pts))
    assert(2 <= pts <= 2^(n-2))
    flip = { '0': '1', '1': '0', '*': '*' }
    if pts == 2:
        H = standard(n)
        if is_odd(n):
            return H
        return Hitting([flip[x[0]] + x[1:] for x in H.F])
    p1 = (pts // 4) * 2
    p0 = pts - p1
    H0 = standard_points_exact(n-1, p0)
    H1 = standard_points_exact(n-1, p1)
    H1f = Hitting([flip[x[0]] + x[1:] for x in H1.F])
    return Hitting([x[1:] + x[0] for x in H0.merge(H1f).F])

def homogeneous_reducible(n, k):
    "possibly reduce tight homogeneous hitting formula on n points with constant codimension k"
    assert(1 <= k <= n < 2^k)
    if k == 1:
        return Hitting(['0', '1'])
    if n <= 2^(k-1):
        H = homogeneous_reducible(n-1, k-1)
        return Hitting([b + x for b in '01' for x in H.F])
    n0 = (n-1)//2
    n1 = (n-1)-n0
    H0 = homogeneous_reducible(n0, k-1)
    H1 = homogeneous_reducible(n1, k-1)
    return Hitting(['0' + x + '*' * n1 for x in H0.F] + ['1' + '*' * n0 + x for x in H1.F])

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