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

def is_hitting(A):
    "determine whether given formula is hitting"
    n = len(A[0])
    m = len(A)
    if any(not disjoint(A[i],A[j]) for i in range(m) for j in range(i)):
        return [(A[i],A[j]) for i in range(m) for j in range(i) if not disjoint(A[i],A[j])]
    return sum(2^nstars(s) for s in A) == 2^n

def is_irreducible(A):
    "determine whether given formula is irreducible"
    n = len(A[0])
    m = len(A)
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

def is_homogeneous(A):
    "determine whether given formula is homogeneous"
    return all(nstars(s) == nstars(A[0]) for s in A)

def split(F, i):
    "recursive construction which splits on the i'th coordinate"
    def split_line(x, i):
        y, b, z = x[:i], x[i], x[i+1:]
        if b == '*':
            return [y + '**' + z + '*']
        else:
            return [y + b + '*' + z + '0', y + '*' + b + z + '1']
    return sum((split_line(x,i) for x in F), [])

def split_all(F):
    "apply split on all coordinates"
    n = len(F[0])
    for i in range(n):
        F = split(F, 2*i)
    return F

def standard(n):
    "standard construction for n >= 3"
    assert(n >= 3)
    F  = ['1'*i + '000' + '*' * (n-3-i) for i in range(n-2)]
    F += ['01' + '*' * (n-2)]
    F += ['1'*i + '*01' + '*' * (n-3-i) for i in range(n-2)]
    F += ['1' * (n-2) + '*0']
    F += ['1' * n]
    return F

def homogeneous4():
    "homogeneous construction for n = 4"
    return ['001*', '0*01', '01*0', '110*', '1*10', '10*1', '*000', '*111']

def special6():
    "construction with many stars for n = 6"
    F  = ['0*0*1*', '1**0*1', '00**0*', '10***0']
    F += ['001*1*', '10*1*1', '010*0*', '11*0*0']
    F += ['*111**', '0110**', '1101**']
    return F
