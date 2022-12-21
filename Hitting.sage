from difflib import restore
import itertools, json

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

def nzeroes(s):
    "compute the coweight of given subcube"
    return len([c for c in s if c == '0'])

def nones(s):
    "compute the weight of given subcube"
    return len([c for c in s if c == '1'])

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

def binary_strings(n):
    "return all binary strings of length n"
    for s in itertools.product('01', repeat = n):
        yield ''.join(s)

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
        #assert(0 <= item < self.m)
        return self.F[item]

    def __eq__(self, other):
        "compare sorted list of subcubes/subspaces"
        assert('F' in dir(other))
        return list(sorted(self.F)) == list(sorted(other.F))

    def dimension_histogram(self):
        "return histogram of number of subcubes of given dimension"
        def histogram(data):
            D = {}
            for x in data:
                if x not in D:
                    D[x] = 0
                D[x] += 1
            return sorted(D.items(), key = lambda kv: kv[0], reverse = True)
        return histogram(self.dimensions())

    def properties(self):
        "return several properties of self"
        res = {}
        res['variables'] = self.n
        res['clauses'] = self.m
        res['dim'] = self.dim()
        res['dimensions'] = self.dimension_histogram()
        res['hitting'] = self.is_hitting()
        res['tight'] = self.is_tight()
        res['irreducible'] = self.is_irreducible()
        res['homogeneous'] = self.is_homogeneous()
        if 'weight_vector' in dir(self):
            res['weights'] = self.weight_vector()
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

    def max_weight(self):
        "return maximal weight of a subcube"
        return max(nones(x) for x in self)

    def weight_vector(self):
        "return weight vector (truncated)"
        w = [0] * (self.max_weight() + 1)
        for x in self:
            w[nones(x)] += 1
        return w

    def sort_by_weight(self):
        "arrange according to weight"
        return Hitting(sorted(self.F, key = lambda x: (self.n+1) * nones(x) + nstars(x)))

    def by_dimension(self):
        "return dictionary with subcubes arranged according to dimension"
        D = dict()
        for x in self:
            dim = nstars(x)
            if dim not in D:
                D[dim] = []
            D[dim].append(x)
        return D

    def rotate(self, rot):
        "rotate left by rot"
        if rot == 0:
            return Hitting(self.F)
        if rot < 0:
            rot = self.n - (-rot)
        return Hitting([x[rot:] + x[:rot] for x in self.F])

    def permute(self, p):
        "permute using given 1-based permutation: x → x(p(1)), ..., x(p(n))"
        return Hitting([''.join(x[i-1] for i in p) for x in self])

    def reverse(self):
        "reverse all subcubes"
        return self.permute(list(range(self.n, 0, -1)))

    def xor(self, mask):
        "xor by mask (string in {0,1}^n)"
        assert(len(mask) == self.n)
        assert(all(c in '01' for c in mask))
        D = {'0': {'*': '*', '0': '0', '1': '1'}, '1': {'*': '*', '0': '1', '1': '0'}}
        return Hitting([''.join(D[m][c] for (m,c) in zip(mask,x)) for x in self])

    def complement(self):
        "complement all subcubes (switch 0s and 1s)"
        return self.xor('1' * self.n)

    def is_permutation(self, other, ret = False):
        "determine whether other is permutation of self; optionally return permutations"
        perms = [p for p in Permutations(self.n) if self.permute(p) == other]
        if ret:
            return perms
        return len(perms) > 0

    def permutation_symmetries(self):
        "return permutation symmetries"
        return self.is_permutation(self, True)

    def is_equivalent(self, other, ret = False):
        "determine whether other is equivalent to self; optionally return group elements"
        elems = [(m,p) for m in binary_strings(self.n) for p in Permutations(self.n) if \
            self.xor(m).permute(p) == other]
        if ret:
            return elems
        return len(elems) > 0

    def automorphisms(self):
        "return automorphisms"
        return self.is_equivalent(self, True)

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

    def star_patterns(self):
        "return counts of star patterns"
        D = self.by_star_pattern()
        return dict((k, len(D[k])) for k in D.keys())

    def compress_subcubes(self, subcubes):
        "compress a list of subcubes into a subspace; return None if impossible"
        subspace = sum((self.subcube_to_subspace(S) for S in subcubes), 0)
        if len(subspace) == 2 * sum(2^nstars(sc) for sc in subcubes):
            return subspace
        return None

    def compress_by_star_pattern(self):
        "compress subcubes by star pattern"
        patterns = self.by_star_pattern()
        return dict((k, self.compress_subcubes(patterns[k])) for k in patterns)

    def to_plus_compressed(self):
        "construct an equivalent HittingPlus instance, compressing pairs of subcubes with the same star pattern"
        subspaces = list(self.compress_by_star_pattern().values())
        if None in subspaces:
            return None
        return HittingPlus(subspaces)
        #patterns = self.by_star_pattern()
        #return HittingPlus([sum((self.subcube_to_subspace(S) for S in val), 0) for val in patterns.values()])

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
        return self.nfs_flip([(i, j)])

    def nfs_flips(self, pairs):
        "flip several nfs pairs at once"
        G = self.F[:]
        for (i, j) in pairs:
            if i > j:
                i, j = j, i
            assert(0 <= i < j < self.m)
            assert(is_nfs_pair(self.F[i], self.F[j]))
            G[i], G[j] = nfs_flip(self.F[i], self.F[j])
        return Hitting(G)

    def nfs_equivalent(self, other, allow_xor = False, wt = 1, ret = False):
        "check whether self is nfs-equivalent to toher using wt nfs-flips; optionally return proof"
        ops = list(itertools.combinations(self.nfs_pairs(), wt))
        ops = [L for L in ops if all(x == y or set(x).isdisjoint(set(y)) for x in L for y in L)]
        if allow_xor:
            method = 'is_equivalent'
        else:
            method = 'is_permutation'
        rets = [(L, getattr(self.nfs_flips(L), method)(other, ret=True)) for L in ops]
        rets = [(L, P) for (L, P) in rets if len(P) > 0]
        if ret:
            return rets
        return len(rets) > 0

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

    def decompress(self, x = None):
        "decompress given subspace, or convert entire formula to a Hitting formula"
        if x is None:
            return Hitting(sum([self.decompress(x) for x in self], []))
        stars = [i for i in range(self.n) if self.V([0] + [int(j==i) for j in range(self.n)]) in x]
        positions = [0] + [i+1 for i in stars]
        points = [p[1:] for p in x if all(p[i] == 1 for i in positions)]
        F = [''.join('*' if i in stars else str(p[i]) for i in range(self.n)) for p in points]
        return F

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

    def intersection(self):
        "return intersection of all subspaces"
        I = self.F[0]
        for S in self.F[1:]:
            I = I.intersection(S)
        return I

    def dim(self):
        "return effective dimension"
        return self. n - self.intersection().dimension()

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
    return Hitting(\
        ['0' * (n-1) + '*'] +\
        ['0' + '*' * i + '1' + '0' * (n-2-i) for i in range(n-2)] +\
        ['1' + '*' * (n-2) + '0'] +\
        ['*' * i + '1' + '0' * (n-2-i) + '1' for i in range(n-1)])

def standard_few1_xor(n, i):
    "constructions with few 1's for n ≥ 3; 0 ≤ i ≤ 5"
    mask = ['0'*n, '0'*(n-1)+'1', '01'+'0'*(n-3)+'1', '1'+'0'*(n-1), '11'+'0'*(n-2), '01'+'0'*(n-2)][i]
    return standard_few1(n).xor(mask)

def standard_few1_xor_iter(n, i):
    "iterative implementation of standard_few1_xor"
    if i == 0:
        G = Hitting(['1*', '00', '01'])
        F0 = Hitting(['01*', '110', '1*1', '*00', '001'])
    elif i == 1:
        G = Hitting(['0*', '10', '11'])
        F0 = Hitting(['11*', '101', '0*1', '*00', '010'])
    elif i == 2:
        G = Hitting(['0*', '10', '11'])
        F0 = Hitting(['11*', '011', '0*0', '*01', '100'])
    elif i == 3:
        G = Hitting(['10', '00', '*1'])
        F0 = Hitting(['1*0', '101', '00*', '010', '*11'])
    elif i == 4:
        G = Hitting(['10', '00', '*1'])
        F0 = Hitting(['1*1', '100', '00*', '011', '*10'])
    elif i == 5:
        G = Hitting(['1*', '00', '01'])
        F0 = Hitting(['01*', '111', '1*0', '*01', '000'])
    return iteration_merge(F0, G, 1, 1, n - 3, False).rotate(1)

def standard_linear(n):
    "standard construction for n ≥ 3, joining the two points"
    H = standard(n).to_plus()
    return HittingPlus([H.F[0] + H.F[-1]] + H.F[1:-1])

def homogeneous(n, k):
    "some construction for given n and codimension k"
    if n == 4 and k == 3:
        return Hitting(['001*', '0*01', '01*0', '110*', '1*10', '10*1', '*000', '*111'])
    if n == 6 and k == 4:
        return Hitting(['0000**', '01**00', '001**1', '01*01*', '0*01*1', '0**110', '10*11*', '10**01', '1101**', '111**0', '1*00*0', '1**011', '*010*0', '*0*100', '*111*1', '*1*001'])
    if n == 6 and k == 5:
        return Hitting(['0000*1', '00011*', '00100*', '0011*0', '001*11', '00*010', '00*101', '01000*', '0101*1', '010*10', '0110*0', '01111*', '011*01', '01*011', '0*0100', '10001*', '1001*1', '1010*0', '10111*', '101*01', '10*100', '1100*0', '11010*', '110*11', '11100*', '1111*1', '111*10', '1*0001', '1*0110', '1*1011', '*00000', '*11100'])
    if n == 7 and k == 5:
        return Hitting(['00000**', '*00010*', '0001**0', '0010**1', '001**10', '00*1*11', '010*01*', '0110*1*', '01*111*', '0*0011*', '0*01*01', '0*10*00', '0*1110*', '10011**', '100*0*0', '1011*1*', '101*10*', '10*00*1', '10*011*', '110**10', '111*1*0', '11*0*11', '11*11*1', '1*010*1', '1*100*0', '*01100*', '*10000*', '*10*100', '*11101*', '*11*001', '*1*0101', '*1*1000'])
    if n == 7 and k == 6:
        return Hitting(['000000*', '*000010', '000011*', '000101*', '00011*1', '001001*', '00101*1', '0011*00', '0011*11', '001*001', '00*0100', '00*1110', '0100*00', '01011*0', '0101*01', '010*010', '010*111', '0110*01', '011100*', '011111*', '011*011', '011*100', '01*0110', '0*00011', '0*00101', '0*01000', '0*10000', '0*11010', '0*11101', '10001*1', '1000*00', '1001*10', '100*011', '10100*0', '1010*11', '101101*', '10111*0', '101*101', '10*0001', '10*1000', '10*1111', '11000*0', '1100*11', '110100*', '110111*', '110*100', '11100*1', '111110*', '1111*11', '111*000', '111*110', '11*0101', '11*1010', '1*00110', '1*01101', '1*10100', '1*11001', '*001001', '*001100', '*010110', '*100001', '*101011', '*110010', '*110111'])
    if n == 8 and k == 6:
        return Hitting(['000000**', '*000010*', '00010*0*', '00011*1*', '000*011*', '001001**', '0010*00*', '001100**', '0011*11*', '001*110*', '00*0111*', '00*1100*', '01000*0*', '0100*11*', '010101**', '0*10101*', '0101*00*', '010*001*', '011000**', '01110*0*', '011110**', '011*011*', '011*11*0', '01*111*1', '0*0010*0', '0*001*01', '100110**', '1001*11*', '100*000*', '10100*0*', '101010**', '10110*1*', '10111*0*', '10*0011*', '10*011*1', '110001**', '110100**', '110*11*1', '11100*1*', '1111*10*', '111*101*', '11*0000*', '11*1011*', '11*1100*', '1*00001*', '1*00100*', '1*001*10', '1*01010*', '1*1011*0', '1*11000*', '1*11111*', '*001001*', '*001110*', '*010001*', '*011010*', '*011101*', '*101101*', '*10111*0', '*110010*', '*110100*', '*11011*1', '*111001*', '**001011', '**001100'])
    if n == 8 and k == 7:
        return Hitting(['0000000*', '*0000010', '000010*1', '0000110*', '0000*110', '0001010*', '00010*10', '0001111*', '00011*01', '0001*011', '000*0111', '000*1000', '001000*0', '0010010*', '00101*01', '0010*011', '001101*1', '0011100*', '00111*11', '0011*010', '0011*100', '001*0001', '001*1110', '00*01010', '00*01111', '0100011*', '01001*11', '0100*010', '0100*100', '010101*0', '01010*11', '010*0000', '010*1101', '010*1110', '011001*0', '01100*01', '0110101*', '011011*1', '0110*000', '0111010*', '01111*01', '01111*10', '0111*111', '011*0011', '01*01001', '01*10010', '01*11000', '01*11011', '0*000011', '0*000101', '0*010001', '0*011010', '0*011100', '0*100111', '0*101100', '0*110000', '0*110110', '100000*1', '1000101*', '100011*0', '1000*000', '1000*111', '10010*11', '100111*1', '10011*00', '1001*001', '1001*010', '100*0101', '100*0110', '1010001*', '101001*1', '10100*00', '1010111*', '101100*0', '1011011*', '10110*01', '101*1001', '101*1010', '101*1100', '10*01101', '10*10100', '10*11011', '10*11110', '1100001*', '1100110*', '11001*10', '110100*1', '11010*10', '110111*0', '1101*000', '110*0100', '110*0111', '110*1011', '11100*11', '111010*0', '11101*01', '1110*100', '1111001*', '111101*1', '11110*00', '111110*1', '1111*110', '11*00000', '11*00101', '11*00110', '11*01111', '11*11010', '11*11101', '1*001001', '1*100001', '1*101011', '1*111000', '1*111111', '*0000100', '*0010000', '*0100110', '*0101000', '*0110011', '*0111101', '*1000001', '*1001000', '*1010101', '*1011001', '*1011111', '*1100010', '*1101110', '*1110001', '*1111100'])

def homogeneous_database():
    "database of known homogeneous constructions"
    return {(n,k): homogeneous(n,k) for (n,k) in [(4,3),(6,4),(6,5),(7,5),(7,6),(8,6),(8,7)]}

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

def standard_homogeneous(base, t):
    "homogeneous construction with t iterations"
    F = base
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

def iteration_merge(F, G, b, rot, iter, final_rotation = True):
    "merge gadget G into F for iter many iterations; put G in position b, and rotate left each time by rot"
    for _ in range(iter):
        G0 = Hitting([x + '*' * (F.n - G.n) for x in G])
        if b == 0:
            F = G0.merge(F)
        else:
            F = F.merge(G0)
        F = F.rotate(rot)
    if final_rotation:
        return F.rotate(-rot)
    else:
        return F

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

def large5():
    "return a tight irreducible formula for n=5 with 40 subcubes"
    F = [''.join(str(d) for d in S) for S in itertools.product([0,1], repeat=5) if\
        S[0] ^^ S[1] ^^ S[2] == S[2] ^^ S[3] ^^ S[4] == 0]
    F += ['001*0', '0101*', '1000*', '111*1']
    F += ['*1001', '*0010', '1*100', '0*111']
    F += ['00*01', '01*00', '10*11', '11*10']
    return Hitting(F)

def large6():
    "return a tight irreducible formula for n=6 with 80 subcubes"
    F = [''.join(str(d) for d in S) for S in itertools.product([0,1], repeat=6) if\
        S[0] ^^ S[1] == S[2] ^^ S[3] == S[4] ^^ S[5]]
    F += ['0010*1', '00011*', '01001*', '0111*0', '1000*1', '10110*', '11100*', '1101*0']
    F += ['*10001', '1*0010', '0*1000', '*11011', '*00100', '1*0111', '0*1101', '*01110']
    F += ['000*01', '00*010', '010*00', '01*111', '10*000', '101*11', '11*101', '111*10']
    return Hitting(F)

###

def decode_kurz(s):
    "decode a hitting formula in Kurz encoding into list of subcubes, convert to Hitting if alphabet is binary"
    parts = [int(t) for t in s.strip().split(' ')]
    alph, n, m, values = *parts[:3], parts[3:]
    assert(len(values) == n * m)
    symbols = ['*' if i == alph else str(i) for i in values]
    subcubes = [''.join(symbols[n*j:n*(j+1)]) for j in range(m)]
    if alph == 2:
        return Hitting(subcubes)
    return subcubes

def decode_kurz_file(name):
    "decode a file containing list of hitting formulas in Kurz format"
    contents = open(name, 'r').read().splitlines()
    return [decode_kurz(s) for s in contents]

###

import xml.etree.ElementTree as ET

def decode_cplex_solution(xml, suppress_check = False):
    "decode xml solution"
    def to_subcube(s):
        i = int(s)
        r = ''
        while i > 0:
            r += '01*'[i % 3]
            i = i // 3
        return r
    vars = xml[3]
    assert(vars.tag == 'variables')
    names = [var.attrib['name'][1:] for var in vars if var.attrib['name'].startswith('x') and var.attrib['value'] == '1']
    subcubes = [to_subcube(s) for s in names]
    n = max(len(s) for s in subcubes)
    subcubes = [s + '0' * (n - len(s)) for s in subcubes]
    return Hitting(subcubes, suppress_check=suppress_check)

# e.g. many_terms_n_6_all.sol
def decode_cplex_file(file_name):
    "decode xml file containing many solutions"
    root = ET.parse(file_name).getroot()
    raw = [decode_cplex_solution(solution, True) for solution in root]
    return [H for H in raw if H.is_hitting()]

def vertex_constraints(H):
    "determine number of affine constraints on set of points"
    V = VectorSpace(GF(2), H.n+1)
    return V.subspace([V([1] + [int(c) for c in pt]) for pt in H.by_dimension()[0]]).codimension()

###

def points_complement(P):
    n = len(P[0])
    return [p for p in [''.join(s) for s in itertools.product('01', repeat=n)] if p not in P]

def points_generate(n, f, g):
    return [''.join(str(q%2) for q in list(L) + [f(L), g(L)])\
        for L in itertools.product([0,1], repeat=n-2)]

def weight_moment(L, k=1):
    return binomial(sum(L), k)

def majority(L):
    n = len(L)
    return int(2*sum(L) > n)

def points_to_edges(points):
    def dist(x,y):
        return sum(a!=b for (a,b) in zip(x,y))
    options = [(x, sum(dist(x,y) == 1 for y in points)) for x in points]
    options = [(x,c) for (x,c) in options if c > 0]
    if len(options) == 0:
        yield points, []
        return
    x = min(options, key=lambda k: k[1])[0]
    ys = [y for y in points if dist(x,y) == 1]
    if len(ys) == 0:
        yield points, []
        return
    for y in ys:
        new_points = [p for p in points if p not in [x,y]]
        for p, e in points_to_edges(new_points):
            yield p, [joins(x,y)] + e

def points_edges_guesses(P, only_irreducible = True):
    for Q in points_to_edges(points_complement(P)):
        F = Hitting(P + Q[0] + Q[1])
        if not only_irreducible or F.is_irreducible():
            yield F