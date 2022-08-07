construction5 = ['0001*',
                '00*01',
                '001*0',
                '1101*',
                '11*01',
                '111*0',
                '0110*',
                '01*10',
                '010*1',
                '1010*',
                '10*10',
                '100*1',
                '**000',
                '**111']

def flip(s):
    return "".join('1' if t == '0' else ('0' if t == '1' else '*') for t in s)


def append2(A, B):
    Aprime = ['00' + x for x in A] + ['11' + x for x in A] + \
             ['01' + flip(x) for x in A] + ['10' + flip(x) for x in A]
    Bprime = ['**' + y for y in B]
    return Aprime, Bprime

A5, B5 = construction5[:-2], construction5[-2:]
A7, B7 = append2(A5, B5)
A9, B9 = append2(A7, B7)

print(len(A9 + B9))
for x in A9 + B9:
    print(x)