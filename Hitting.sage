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

class Hitting:
    def __init__(self, F):
        "init class with a list of strings over 0/1/*"
        self.F = F
        n = self.n = len(F[0])
        m = self.m = len(F)
        assert(self.is_hitting())

    def __repr__(self):
        return f'Hitting({repr(self.F)})'

    def is_hitting(self):
        "determine whether given formula is hitting"
        n, m, A = self.n, self.m, self.F
        if any(not disjoint(A[i],A[j]) for i in range(m) for j in range(i)):
            return [(A[i],A[j]) for i in range(m) for j in range(i) if not disjoint(A[i],A[j])]
        return sum(2^nstars(s) for s in A) == 2^n

    def is_irreducible(self):
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
                if s != '*' * n: return s
        return True

    def is_homogeneous(self):
        "determine whether given formula is homogeneous"
        return all(nstars(s) == nstars(self.F[0]) for s in self.F)

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

def standard(n):
    "standard construction for n >= 3"
    assert(n >= 3)
    F  = ['1'*i + '000' + '*' * (n-3-i) for i in range(n-2)]
    F += ['01' + '*' * (n-2)]
    F += ['1'*i + '*01' + '*' * (n-3-i) for i in range(n-2)]
    F += ['1' * (n-2) + '*0']
    F += ['1' * n]
    return Hitting(F)

def homogeneous4():
    "homogeneous construction for n = 4"
    return Hitting(['001*', '0*01', '01*0', '110*', '1*10', '10*1', '*000', '*111'])

def special6():
    "construction with many stars for n = 6"
    F  = ['0*0*1*', '1**0*1', '00**0*', '10***0']
    F += ['001*1*', '10*1*1', '010*0*', '11*0*0']
    F += ['*111**', '0110**', '1101**']
    return Hitting(F)