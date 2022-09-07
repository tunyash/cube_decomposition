from itertools import product, combinations
from typing import List, Tuple

def take_log(two_to_n: int) -> int:
    n = 1
    while 2**n < two_to_n:
        n += 1
    return n


def is_cert_complexity_k(f: List[int], k: int, sign: int) -> bool:
    n = take_log(len(f))
    covered = [v != sign for v in f]
    for t in combinations(range(n), k):
        for signs in product([0,1], repeat=k):
            must_be_one = sum(2**i for (i, j) in zip(t, signs) if j == 1)
            must_be_zero = sum(2**i for (i, j) in zip(t, signs) if j == 0)
            good_cert = True
            points = []
            for i in range(2**n):
                if (i & must_be_one == must_be_one) and ((2**n-1-i) & must_be_zero == must_be_zero):
                    points.append(i)
                    if f[i] != sign:
                        good_cert = False
                        break
            if good_cert:
                for p in points:
                    covered[p] = True
    return all(covered)

def find_cert_complexity(f: List[int], sign: int) -> int:
    n = take_log(len(f))
    if all([v == sign for v in f]):
        return 0
    for k in range(1, n):
        if is_cert_complexity_k(f, k, sign):
            return k
    return n

def find_minterms(f: List[int]) -> List[int]:
    n = take_log(len(f))
    answer = []
    for i, v in enumerate(f):
        if f[i] == 0:
            continue
        minterm = True
        for j in range(n):
            if (i & (1<<j)) != 0:
                if f[i ^ (1<<j)] == 1:
                    minterm = False
                    break
        if minterm:
            answer.append(i)
    return answer

def compute_pyramid_function(mask: int, n: int) -> int:
    t = [(mask>>i) & 1 for i in range(n)]
    operation = 0
    while len(t) > 1:
        t = [(cur & next) if operation == 1 else (cur | next) for cur, next in zip(t[:-1], t[1:])]
        operation ^= 1
    return t[0]

def get_sensitive_bits(f: List[int]) -> List[int]:
    n = take_log(len(f))
    return [j for j in range(n) if any(f[i] != f[i ^ (1<<j)] for i in range(2**n))]

# f = [0]*8 + [1]*8
# print(find_minterms(f))
#
# print(find_cert_complexity(f, 1))
n = 17
pyramid = [compute_pyramid_function(i, n) for i in range(2**n)]
print(find_minterms(pyramid))
print(find_cert_complexity(pyramid, 0))
for i, v in enumerate(pyramid):
    print(i, v)

print(get_sensitive_bits(pyramid))