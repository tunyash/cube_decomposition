from itertools import product, combinations

def unite(a, b):
    assert len(a) == len(b)
    return "".join('*' if x != y or x == '*' else x for x,y in zip(a, b))

def within(a, b):
    assert len(a) == len(b)
    return all(y == '*' or x == y for x, y in zip(a, b))

def intersects(a, b):
    assert len(a) == len(b)
    return all(x == '*' or y == '*' or x == y for x, y in zip(a, b))

def is_reducible(masks):
    n = len(masks)
    for i, j in product(range(n), repeat=2):
        if i >= j: 
            continue
        cur = unite(masks[i], masks[j])
        while True:
            enlarged = False
            for k in range(n):
                if intersects(masks[k], cur) and not within(masks[k], cur):
                    cur = unite(cur, masks[k])
                    enlarged = True
            if not enlarged:
                break
        if '0' in cur or '1' in cur:
            return True, cur
    return False, ""

def is_hitting(masks):
    covered = 0
    for i in masks:
        covered += 2**sum(1 if z=='*' else 0 for z in i)
    if covered != 2**len(masks[0]):
        return False
    for i, j in combinations(masks, 2):
        if intersects(i, j):
            return False
    return True

n = int(input())
masks = []
for i in range(n):
    masks.append(input())

if not is_hitting(masks):
    print('Not hitting')

answer, example = is_reducible(masks)
if answer:
    for mask in masks:
        assert within(mask, example) or not intersects(mask, example)

if answer:
    print('Recudible: ', example)
else:
    print('Irreducible')