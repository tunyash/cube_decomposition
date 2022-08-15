# Checks where a given point is in a cube composition

def fit(s, mask):
    return all(c == mc or mc == '*' for c, mc in zip(s, mask))

n = int(input())
hitting = []
for i in range(n):
    hitting.append(input())

s = input()
for mask in hitting:
    if fit(s, mask):
        print(mask)