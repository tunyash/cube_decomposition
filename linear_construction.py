def flip(s):
    return "".join('1' if t == '0' else ('0' if t == '1' else '*') for t in s)

def genBC(B):
    n = len(B[0]) + 1
    C = ['1' + flip(s[:2]) + s[2:] for s in B]
    Bprime = ['010' + '*'*(n-3), '*11' + '*'*(n-3)] + C   
    return Bprime

B3 = ['1*0', '*11', '010', '101']
n = int(input())
B = B3
for i in range(4, n+1):
    B = genBC(B)

B += ['00' + '*' * (n-2)]

print(len(B))
for mask in B:
    print(mask)