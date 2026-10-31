# Audit of the outside framework "Frodo", theorem T3 step (ii) (log §34.3z⁵⁵): expand ν(μ(a, z)), a = μ(x, y), x, y, z
# primitive, by the bialgebra law B1 and by the Leibniz law DA1, over free nonassociative terms with unit e.
from collections import Counter
E='e'
def mu(s,t):
    if s==E: return t
    if t==E: return s
    return ('m',s,t)
prim={'x':[('x',E),(E,'x')],'y':[('y',E),(E,'y')],'z':[('z',E),(E,'z')],E:[(E,E)]}
def nuB1_mu(s,t,ns,nt):   # B1: nu(mu(s,t)) = sum mu(s1,t1) (x) mu(s2,t2)
    return Counter((mu(a,c),mu(b,d)) for a,b in ns for c,d in nt)
def nuDA1_mu(s,t,ns,nt):  # DA1: s1 (x) mu(s2,t)  +  mu(s,t1) (x) t2
    C=Counter((a,mu(b,t)) for a,b in ns); C.update((mu(s,c),d) for c,d in nt); return C
a=mu('x','y')
na=list(nuB1_mu('x','y',prim['x'],prim['y']).elements())
print("nu(a) by B1 :",dict(nuB1_mu('x','y',prim['x'],prim['y'])))
print("nu(a) by DA1:",dict(nuDA1_mu('x','y',prim['x'],prim['y'])))
B=nuB1_mu(a,'z',na,prim['z']); D=nuDA1_mu(a,'z',na,prim['z'])
print("branches B1, DA1:",sum(B.values()),sum(D.values()))
print("B1 - DA1 :",dict(B-D)); print("DA1 - B1 :",dict(D-B))
print("seed: DA1 at (e,e):",dict(nuDA1_mu(E,E,prim[E],prim[E])),"vs nu(e) =",prim[E])
