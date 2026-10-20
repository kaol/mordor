"""M_omega example for log §34.3o: a monotone F on a height-2 lattice whose (meet, join, F)-closure of {bot, top}
is infinite (checked here on truncations M_n), although the Cut Lemma holds there (edge-height <= 5)."""
# M_n truncation of the M_omega example: bot='b', top='t', atoms 0..n-1
def run(n):
    E = ['b', 't'] + list(range(n))
    le = lambda x, y: x == y or x == 'b' or y == 't'
    def F(x, y):
        if x == 'b': return 0 if y == 't' else 'b'
        if x == 't': return 'b' if y == 'b' else 't'
        if y == 'b': return 'b'
        if y == 't': return 't'
        return (x + 1 if x + 1 < n else 't') if y == x else 'b'
    mono = all(le(F(x, y), F(x2, y2)) for x in E for y in E for x2 in E for y2 in E if le(x, x2) and le(y, y2))
    S = {'b', 't'}
    def meet(x, y): return x if le(x, y) else y if le(y, x) else 'b'
    def join(x, y): return y if le(x, y) else x if le(y, x) else 't'
    while True:
        new = S | {F(x, y) for x in S for y in S} | {meet(x, y) for x in S for y in S} | {join(x, y) for x in S for y in S}
        if new == S: break
        S = new
    print(n, 'monotone', mono, 'closure size', len(S), 'of', len(E))
for n in (3, 5, 8, 12): run(n)
