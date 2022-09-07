n = int(input())
s = []
for i in range(n):
    s.append(input())

def make_step(strs, columns):
    if len(columns) == 0:
        return strs
    res = []
    t = columns[0]    
    for s in strs:
        exs = s[:t] + s[t+1:]
        if s[t] == '*':
            res.append(exs+'***')
        else:
            res.append(exs+s[t]+'*0')
            res.append(exs+'*'+s[t]+'1')
    return make_step(res, columns[1:])

res = make_step(s, list(range(len(s[0]))))
print(len(res))
for s in res:
    print(s)