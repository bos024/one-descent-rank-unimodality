"""Exact QA of WRITTEN unbounded theorems, not a universal LC certificate.

References are independently rebuilt as all proper suffix S-products plus
the full S-product times H. Positive-root and conjugate-root calculations
use integer pairs in Q(phi); no floating comparisons are used.
"""
from pathlib import Path
from collections import Counter
from itertools import accumulate,product
from random import Random
import hashlib,json,time
from audit_arbitrary_Fibonacci_tail_late_C import (
    append_reference,numerator_append,evaluate,add,sub,mul,power,sign,absolute,
    PHI,NEGPHI,CONJ)
from audit_minimum_staircase_scaled_dyadic import arm_prefix

ROOT=Path(__file__).resolve().parent
Q=( -1,1)  # phi-1 = 1/phi


def s_product(P,t):
    out=[0]*(len(P)+t);v=0
    for n in range(1,len(out)):
        if n-1<len(P):v+=P[n-1]
        if n-t-1>=0 and n-t-1<len(P):v-=P[n-t-1]
        out[n]=v
    return out


def rebuild(V,N):
    P=[1];proper=[0]*(N+1)
    for t in reversed(V):
        for i,c in enumerate(P[:N+1]):proper[i]+=c
        P=s_product(P,t)
    response=[]
    for n in range(N+1):
        response.append((P[n] if n<len(P) else 0)+
                        (response[n-1] if n else 0)+
                        (response[n-2] if n>1 else 0))
    return [proper[n]+response[n] for n in range(N+1)]


def c_minimum(F,D,lo,hi,counts,literal=False):
    G=list(accumulate(F));best=1
    for N in range(4,hi+1):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        if N<lo:continue
        assert G[best]*D[N-1]>=G[best-1]*D[N],('C',N,best)
        counts['exact_prefix_minimum_all_shift_C_payments']+=1
        counts['logical_shift_coverage']+=N-3
        if literal:
            for k in range(1,N-2):
                assert G[k]*D[N-1]>=G[k-1]*D[N],('literal',N,k)
                counts['literal_all_shift_C_products']+=1


def main():
    started=time.monotonic();rng=Random(20261028931);counts=Counter();sha=hashlib.sha256()
    words=[]
    for r in range(1,5):
        words.extend(V for V in product(range(2,9),repeat=r) if V[0]>=3)
    for _ in range(1600):
        r=rng.randint(1,20)
        words.append(tuple([rng.randint(3,85)]+rng.choices(range(2,86),k=r-1)))
    for wi,V in enumerate(words):
        W=sum(V);N=W+12;fib=[0,1]
        for n in range(2,N+5):fib.append(fib[-1]+fib[-2])
        F=[fib[n+1] for n in range(N+1)];B=[1];A=(1,0);C=(1,0)
        for t in V:
            F=append_reference(F,t);B=numerator_append(B,t)
            pwin=evaluate([0]+[1]*t,Q);mwin=evaluate([0]+[1]*t,NEGPHI)
            assert sign(sub(mul(power(PHI,t),pwin),mul(PHI,absolute(mwin))))>=0
            A=mul(A,pwin);C=mul(C,mwin)
            counts['all_capacity_relative_spectral_norm_steps']+=1
        assert F==rebuild(V,N),('independent reference',V)
        assert A==evaluate(B,Q) and C==evaluate(B,NEGPHI)
        assert sign(sub(mul(power(PHI,W),A),mul(power(PHI,len(V)),absolute(C))))>=0
        assert sign(C)==(-1)**W
        D=[1]+[F[n]-F[n-1] for n in range(1,N+1)];G=list(accumulate(F))
        for n in range(W+1,N+1):
            error=sub((D[n],0),mul(PHI,(D[n-1],0)))
            scaled=mul(error,power(PHI,n-2));expected=C if n%2==0 else (-C[0],-C[1])
            assert scaled==expected,('homogeneous atom boundary',V,n)
            J=(fib[n]-1)*D[n-1]-(fib[n-1]-1)*D[n]
            assert J>=0,('binary envelope',V,n,J)
            sigma=(-1)**(n-2)
            formula=sub(mul(A,sub(power(PHI,n-3),mul((sigma,0),Q))),
                mul(mul((sigma,0),C),mul(PHI,sub((1,0),power(Q,n-2)))))
            assert mul((-1,2),(J,0))==formula,('exact spectral determinant',V,n)
            if n==W+1:assert sign(error)<0
            if n>=W+2 and (len(V)>=2 or n>=W+3):
                assert sign(sub(mul(A,power(PHI,n-4)),absolute(C)))>=0
                counts['exact_homogeneous_relative_amplitude_budgets']+=1
            if len(V)==1 and n==W+2:assert J==0
            counts['exact_binary_cumulative_vs_reference_slope_determinants']+=1
        for k in range(1,N+1):
            assert G[k]*(fib[k+2]-1)>=G[k-1]*(fib[k+3]-1)
            counts['all_read_binary_cumulative_envelopes']+=1
        c_minimum(F,D,W+1,N,counts,literal=wi%173==0)
        sha.update(json.dumps([V,B,F],separators=(',',':')).encode())
        counts['independently_rebuilt_arbitrary_order_reference_words']+=1
    # The first shared equality is easy to mishandle as a strict comparison.
    F=rebuild((3,3),10);D=[1]+[F[n]-F[n-1] for n in range(1,len(F))]
    assert D[7:9]==[12,20] and 20*D[7]-12*D[8]==0
    for case in range(1200):
        V=sorted(rng.choices(range(3,24),k=rng.randint(1,9)));W=sum(V);r=len(V);h=W-r
        u=h+rng.randint(1,9);alpha=rng.choice([1,2,3,h+1,u+h+1]);M=2*u+W+1
        F=arm_prefix(alpha,[2]*u+V,M);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,M+1)]
        ell=D.index(max(D));N0=u+r+2;ref=rebuild(V,M)
        rd=[1]+[ref[n]-ref[n-1] for n in range(1,M+1)]
        A=rd[W+2]**2-rd[W+1]*rd[W+3];delta=2 if alpha==1 else 1
        assert A>0 and rd[W+2]>=A and rd[W+4]>=2*A+1
        assert F[:N0]==ref[:N0] and ref[N0]-F[N0]==delta
        n=N0-1;minor=D[n]**2-D[n-1]*D[n+1]
        assert minor==(-1)**(n-W)*A+delta*rd[n-1] and minor>=0
        b,c,d=rd[N0-2:N0+1];k0=N0-3
        assert F[k0:k0+3]==[c,d,c+d]
        assert c*(c+d)-d*(d-delta)==(-1)**(N0-1-W)*A+delta*d>=0
        for n in range(u+r+1,ell):
            assert D[n]**2>=D[n-1]*D[n+1],('entranceLC finite diagnostic',V,u,alpha,n)
            counts['finite_only_sharpened_rising_tail_LC_minors']+=1
        c_minimum(F,D,W+1,M-1,counts,literal=case%131==0)
        # Validate every intermediate step of the new F/G integration, for
        # actual increasing current slopes AFTER the first defect.
        G=list(accumulate(F))
        for n in range(N0+1,ell+1):
            if D[n]<=D[n-1]:continue
            cur,prev=D[n],D[n-1]
            assert cur*c<=prev*(d-delta)
            for i in range(k0+1,n-2):
                assert F[i]*prev>=F[i-1]*cur,('ordinary integration',V,n,i)
                assert G[i]*prev>=G[i-1]*cur,('cumulative integration',V,n,i)
                counts['exact_new_ordinary_and_cumulative_integration_steps']+=1
        sha.update(json.dumps([V,u,alpha,F,D,ell],separators=(',',':')).encode())
        counts['sharpened_actual_contexts']+=1
    out=dict(status='PASS_EXACT_HOMOGENEOUS_REFERENCE_C_AND_SHARP_ENTRANCE_QA',
        counts=dict(counts),state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        written_theorems=['homogeneous_reference_complete_C.tex','sharpened_multitail_single_entrance.tex'],
        scope='Unbounded written theorem with scoped Lean kernels. QA independently rebuilds reference coefficients. Arbitrary CI entrance LC remains OPEN; tested actual LC is finite diagnostic only. General C/A2/original UI remain OPEN; no original least-counterexample bound upgrade.')
    (ROOT/'audit_homogeneous_reference_and_sharp_entrance.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
