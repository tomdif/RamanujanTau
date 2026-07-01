# Truncated power series over Z, index = power of q, truncate at N terms (q^0..q^{N-1}).
N = 26
def zero(): return [0]*N
def one():
    a=zero(); a[0]=1; return a
def add(a,b): return [a[i]+b[i] for i in range(N)]
def sub(a,b): return [a[i]-b[i] for i in range(N)]
def mul(a,b):
    c=zero()
    for i in range(N):
        if a[i]==0: continue
        for j in range(N-i):
            c[i+j]+=a[i]*b[j]
    return c
def scal(k,a): return [k*x for x in a]
def xpow(e):
    a=zero()
    if e<N: a[e]=1
    return a
def pinv(a):
    # inverse of series with a[0]=1
    assert a[0]==1
    b=zero(); b[0]=1
    for n in range(1,N):
        s=0
        for k in range(1,n+1):
            s+=a[k]*b[n-k]
        b[n]=-s
    return b
def onePlusXk(k):  # 1 + q^k
    a=one()
    if k<N: a[k]+=1
    return a
def oneMinusXk(k): # 1 - q^k
    a=one()
    if k<N: a[k]-=1
    return a
def prod(facts):
    r=one()
    for f in facts: r=mul(r,f)
    return r

def qfac(m):   return prod([oneMinusXk(k+1) for k in range(m)])      # (q;q)_m
def q2fac(m):  return prod([oneMinusXk(k+2) for k in range(m)])      # (q^2;q)_m
def oddFac(m): return prod([oneMinusXk(2*k+1) for k in range(m)])    # (q;q^2)_m
def negOddFac(m): return prod([onePlusXk(2*k+1) for k in range(m)])  # (-q;q^2)_m
def negQfac(m): return prod([onePlusXk(k+1) for k in range(m)])      # (-q;q)_m

# a=q Bailey inversion: beta_n = sum_{r<=n} alpha_r * pinv(qfac(n-r)) * pinv(q2fac(n+r))
# => alpha_n = q2fac(2n) * ( beta_n - sum_{r<n} alpha_r*pinv(qfac(n-r))*pinv(q2fac(n+r)) )
def aq_alpha(beta, upto):
    alphas=[]
    for n in range(upto+1):
        acc=beta(n)
        for r in range(n):
            acc=sub(acc, mul(alphas[r], mul(pinv(qfac(n-r)), pinv(q2fac(n+r)))))
        alphas.append(mul(q2fac(2*n), acc))
    return alphas

def show(a, deg=12):
    terms=[]
    for i in range(min(deg+1,N)):
        if a[i]!=0: terms.append(f"{a[i]:+d}q^{i}" if i else f"{a[i]:+d}")
    return " ".join(terms) if terms else "0"

# sanity: seed beta_n = pinv(qfac n)*pinv(q2fac n) must give alpha = delta_{n,0}
seed = lambda n: mul(pinv(qfac(n)), pinv(q2fac(n)))
al=aq_alpha(seed,5)
print("SEED CHECK (expect delta_{n,0}):")
for n,a in enumerate(al): print(f"  a[{n}] = {show(a)}")

cands = {
  "beta_n = 1/(-q;q)_n           ": lambda n: pinv(negQfac(n)),
  "beta_n = (-q;q^2)_n           ": lambda n: negOddFac(n),
  "beta_n = 1/(q;q^2)_n          ": lambda n: pinv(oddFac(n)),
  "beta_n = 1/(q^2;q^2)_n        ": lambda n: pinv(prod([oneMinusXk(2*(k+1)) for k in range(n)])),
  "beta_n = 1/(q;q)_n            ": lambda n: pinv(qfac(n)),
  "beta_n = 1 (const)            ": lambda n: one(),
}
for name,beta in cands.items():
    al=aq_alpha(beta,6)
    print(f"\n=== {name} ===")
    for n,a in enumerate(al):
        print(f"  a[{n}] = {show(a,14)}")

print("\n\n########## CLOSED-FORM + FINAL-IDENTITY VERIFICATION ##########")
# Claim A: for beta_n = 1/(q^2;q^2)_n, alpha_n = (-1)^n q^{n^2} (1+q+..+q^{2n})
def alphaA_closed(n):
    s=zero()
    for k in range(2*n+1):
        e=n*n+k
        if e<N: s[e]+= (1 if n%2==0 else -1)
    return s
betaA = lambda n: pinv(prod([oneMinusXk(2*(k+1)) for k in range(n)]))
alA = aq_alpha(betaA, 7)
okA = all(alA[n]==alphaA_closed(n) for n in range(6))
print("Claim A (alpha closed form) matches computed:", okA)

# Claim B: for beta_n = 1/(q;q)_n, alpha_n = (-1)^n q^{n(3n+1)/2} (1+q+..+q^{2n})
def alphaB_closed(n):
    s=zero()
    base=n*(3*n+1)//2
    for k in range(2*n+1):
        e=base+k
        if e<N: s[e]+= (1 if n%2==0 else -1)
    return s
betaB = lambda n: pinv(qfac(n))
alB = aq_alpha(betaB, 6)
okB = all(alB[n]==alphaB_closed(n) for n in range(5))
print("Claim B (alpha closed form) matches computed:", okB)

# Final identity A: Sum_{n>=0} q^{n^2+n}/(q^2;q^2)_n  ==  (1/(q;q)_inf) Sum_{n in Z} (-1)^n q^{2n^2+n}
# LHS
def tsumQ(beta, upto):  # Sum q^{n^2+n} beta_n
    s=zero()
    for n in range(upto+1):
        s=add(s, mul(xpow(n*n+n), beta(n)))
    return s
LHS_A = tsumQ(betaA, 12)
# RHS
qfacInf = qfac(N-1)   # (q;q)_inf truncated
invqfacInf = pinv(qfacInf)
bilat = zero()
for n in range(-8,9):
    e=2*n*n+n
    if 0<=e<N: bilat[e]+= (1 if n%2==0 else -1)
RHS_A = mul(invqfacInf, bilat)
print("Final identity A  LHS == RHS (to q^24):", LHS_A==RHS_A)
print("  LHS:", show(LHS_A,20))
print("  RHS:", show(RHS_A,20))

# Also identity B: Sum q^{n^2+n}/(q;q)_n == (1/(q;q)_inf) Sum_{n in Z} (-1)^n q^{(5n^2+3n)/2}  (RR2-type)
LHS_B = tsumQ(betaB, 12)
bilatB = zero()
for n in range(-8,9):
    e=(5*n*n+3*n)//2
    if 0<=e<N: bilatB[e]+= (1 if n%2==0 else -1)
RHS_B = mul(invqfacInf, bilatB)
print("Final identity B (RR2)  LHS == RHS (to q24):", LHS_B==RHS_B)
print("  LHS:", show(LHS_B,20))
print("  RHS:", show(RHS_B,20))
