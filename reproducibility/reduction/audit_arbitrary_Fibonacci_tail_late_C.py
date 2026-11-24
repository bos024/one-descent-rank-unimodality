"""Exact Q(sqrt(5)) diagnostics of the unregistered arbitrary-tail late-C proof."""
from pathlib import Path
from random import Random
from collections import Counter
from itertools import accumulate
import json,time
ROOT=Path(__file__).resolve().parent


def add(x,y):return x[0]+y[0],x[1]+y[1]
def neg(x):return -x[0],-x[1]
def sub(x,y):return add(x,neg(y))
def mul(x,y):
    a,b=x;c,d=y
    return a*c+b*d,a*d+b*c+b*d
def power(x,n):
    v=(1,0)
    while n:
        if n&1:v=mul(v,x)
        x=mul(x,x);n//=2
    return v
def sign(x):
    a,b=x;A=2*a+b;B=b
    if B==0:return (A>0)-(A<0)
    if A>=0 and B>=0:return 1
    if A<=0 and B<=0:return -1
    diff=A*A-5*B*B
    return ((diff>0)-(diff<0)) if A>0 else ((diff<0)-(diff>0))
def absolute(x):return x if sign(x)>=0 else neg(x)
PHI=(0,1);CONJ=(1,-1);NEGPHI=(0,-1)


def append_reference(F,t):
    G=[1]+[0]*(len(F)-1);total=0
    for n in range(1,len(F)):
        total+=F[n-1]
        if n>t:total-=F[n-t-1]
        G[n]=total
    return G


def numerator_append(B,t):
    # Independent positive recurrence on T=B-1.
    T=B[:];T[0]-=1;G=[1]+[0]*(len(B)+t-1);total=0
    for n in range(1,len(G)):
        if n-1<len(T):total+=T[n-1]
        if n>t and n-t-1<len(T):total-=T[n-t-1]
        G[n]=total+int(3<=n<=t)
    return G


def evaluate(B,x):
    value=(0,0)
    for a in reversed(B):value=add(mul(value,x),(a,0))
    return value


def main():
    start=time.monotonic();rng=Random(20261028621);counts=Counter()
    assert sign(sub(PHI,(1,0)))>0 and sign(sub((5,0),mul((3,0),PHI)))>0
    assert mul(PHI,CONJ)==(-1,0) and mul(PHI,PHI)==add(PHI,(1,0))
    for case in range(1200):
        V=[] if case==0 else [2]*rng.randint(1,35) if case%5==0 else sorted(rng.choices(range(2,65),k=rng.randint(1,15)))
        if case%2:rng.shuffle(V)
        Wfull=sum(V);first_nonbinary=next((i for i,t in enumerate(V) if t>2),len(V))
        W=sum(V[first_nonbinary:]);N=W+18;F=[1,1]
        for n in range(2,N+1):F.append(F[-1]+F[-2])
        B=[1];conjugate=(1,0);weight=0
        for t in V:
            B=numerator_append(B,t);F=append_reference(F,t);weight+=t
            s=sum((power(NEGPHI,j)[0] for j in range(1,t+1))),sum((power(NEGPHI,j)[1] for j in range(1,t+1)))
            assert mul(PHI,s)==sub(power(NEGPHI,t),(1,0))
            assert sign(sub(power(PHI,t),absolute(s)))>=0
            conjugate=mul(conjugate,s)
            assert conjugate==evaluate(B,NEGPHI)
            assert sign(sub(power(PHI,weight),absolute(conjugate)))>=0
            degree=max(i for i,b in enumerate(B) if b)
            assert sign(sub(power(PHI,degree),absolute(conjugate)))>=0
            counts['ALL_exact_capacity_window_norm_and_numerator_steps']+=1
        degree=max(i for i,b in enumerate(B) if b);B=B[:degree+1]
        assert min(B)>=0 and B[0]==1 and not any(B[1:3]) and degree==W
        counts['leading_binary_fixed_point_weight_reductions']+=W<Wfull
        counts['ALL_exact_effective_numerator_degrees']+=1
        computed=[F[n]-(F[n-1] if n else 0)-(F[n-2] if n>=2 else 0) for n in range(N+1)]
        assert computed==B+[0]*(N+1-len(B))
        counts['ALL_exact_positive_Fibonacci_numerator_reads']+=N+1
        D=[1]+[F[n]-F[n-1] for n in range(1,N+1)];G=list(accumulate(F))
        assert D[1]==0 and all(d>0 for d in D[2:])
        for k in range(N+1):
            margin=(G[k],-(G[k-1] if k else 0))
            assert sign(sub(mul((3,0),margin),(1,0)))>=0
            counts['ALL_exact_uniform_golden_cumulative_margin_reads']+=1
        for n in range(W+6,N+1):
            error=(D[n],-D[n-1]);scaled=mul(error,power(PHI,n-2))
            expected=conjugate if (n-2)%2==0 else neg(conjugate)
            assert scaled==expected
            assert sign(sub((1,0),mul((6,0),absolute(error))))>0
            assert D[n-1]==F[n-3] and G[n-4]==F[n-2]-sum(B)
            assert G[n-4]<=2*D[n-1]
            counts['ALL_exact_scaled_conjugate_error_and_tail_identities']+=1
            for R in range(3,n+3):
                k=n-R;g=G[k] if k>=0 else 0;gp=G[k-1] if k>=1 else 0
                minor=g*D[n-1]-gp*D[n]
                assert minor>=0 and (k<0 or minor>0)
                counts['ALL_literal_late_reference_C_shifts']+=1
        counts['arbitrary_capacity_tail_reference_contexts']+=1
        counts['unordered_tail_contexts']+=V!=sorted(V)
    out=dict(status='PASS_EXACT_ARBITRARY_FIBONACCI_TAIL_LATE_C_QA',counts=dict(counts),
        seconds=time.monotonic()-start,
        scope='Unregistered finite exact QA ONLY. All irrational comparisons performed in Q(sqrt5) with integer-squared sign tests, NO floatingpoint. W=EXACTnumeratordegree=sumcapacitiesAFTERleadingtwosremoved, usingbinaryfixedpoint. Analytic ALL-word late-C proof under formal validation; early N<=W+5/general referenceC/finite-actual transfer/general original C/A2/UI remain OPEN.')
    (ROOT/'audit_arbitrary_Fibonacci_tail_late_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
