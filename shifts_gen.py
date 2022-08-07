from itertools import product

m = int(input())
n = 2 * m + 1
a = '0'*m + '1' + '*'*m
shifts = [a]
for i in range(n - 1):
    prev = shifts[-1]
    shifts.append(prev[-1] + prev[:-1])

rest = []
for z in product(['0', '1'], repeat=n):
    s = list(z)
    if all(not all(x == y or y == '*' for x,y in zip(s, shift)) for shift in shifts):
        rest.append("".join(s))

print(len(rest + shifts))
for x in shifts + rest:
    print(x)