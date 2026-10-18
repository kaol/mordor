"""I5 in the thin model (foundations v3.8): does F(x, y) = g(x) join/meet h(y) (separated variables) force m = n?
No: counts of violators over all monotone g, h on chains 3-5, M3, N5. Lean: Axioms.Source.i5_sep_false."""
import itertools
def mono_maps(n, le):
    R=range(n)
    for t in itertools.product(R, repeat=n):
        if all(le[t[i]][t[j]] for i in R for j in R if le[i][j]): yield t
def lfp(f, n, le, bot):
    x=bot
    while True:
        y=f(x)
        if y==x: return x
        x=y
def chain(n): return [[i<=j for j in range(n)] for i in range(n)]
def run(n, le, join, meet, bot, top, name):
    maps=list(mono_maps(n,le)); bad={'join':0,'meet':0}; tot=0
    for g in maps:
        for h in maps:
            for op in ('join','meet'):
                Fop = join if op=='join' else meet
                F=lambda x,y: Fop[g[x]][h[y]]
                a=[lfp(lambda Y: F(x,Y), n, le, top) for x in range(n)]  # descending from top = gfp (finite)
                b=[lfp(lambda X: F(X,y), n, le, bot) for y in range(n)]
                m=lfp(lambda x: a[x], n, le, bot); nn=lfp(lambda y: b[y], n, le, top)
                if m!=nn: bad[op]+=1
                tot+=1
    print(name, len(maps), 'maps; violations of m=n:', bad, 'of', tot)
for n in (3,4,5):
    le=chain(n); j=[[max(x,y) for y in range(n)] for x in range(n)]; mt=[[min(x,y) for y in range(n)] for x in range(n)]
    run(n, le, j, mt, 0, n-1, f'chain{n}')
# M3 and N5
def lat(elems_le):
    n=len(elems_le); le=elems_le
    def jn(x,y): ub=[z for z in range(n) if le[x][z] and le[y][z]]; return [z for z in ub if all(le[z][w] for w in ub)][0]
    def mt(x,y): lb=[z for z in range(n) if le[z][x] and le[z][y]]; return [z for z in lb if all(le[w][z] for w in lb)][0]
    return [[jn(x,y) for y in range(n)] for x in range(n)], [[mt(x,y) for y in range(n)] for x in range(n)]
M3=[[i==j or i==0 or j==4 for j in range(5)] for i in range(5)]
J,Mt=lat(M3); run(5,M3,J,Mt,0,4,'M3')
# N5: 0<a<b<1, 0<c<1 : 0,a=1,b=2,c=3,1=4
N5le=[[False]*5 for _ in range(5)]
for i,j in [(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)]: N5le[i][j]=True
J,Mt=lat(N5le); run(5,N5le,J,Mt,0,4,'N5')
