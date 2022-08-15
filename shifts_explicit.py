from itertools import product

m = int(input())
n = 2 * m + 1
a = '0'*m + '1' + '*'*m
shifts = [a]
for i in range(n - 1):
    prev = shifts[-1]
    shifts.append(prev[-1] + prev[:-1])

for i,j,k in product(range(m), repeat=3):
    if max(i, k) > m - 1 - j:
        continue
    shifts.append('0'*i + '1' + '*'*j + '0'*k + '1' + '*'*(m-1-j-k) + '0'*j + '1' + '*'*(m-1-i-j))

shifts.append('0'*n)

print(len(shifts))
for shift in shifts:
    print(shift)