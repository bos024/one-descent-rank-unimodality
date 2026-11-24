"""Exact QA of infinite padding and its specified large-padding corollary."""
from pathlib import Path
from random import Random
from math import comb
from collections import Counter
import hashlib,json,time
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import (
    add,sub,mul,power,sign,evaluate,absolute)
from audit_arbitrary_Fibonacci_tail_late_C import append_reference
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from itertools import accumulate

ROOT=Path(__file__).resolve().parent
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ONE=(1,0);ZERO=(0,0)


def binary(m):
    return [sum(comb(k,n-k) for k in range((n+1)//2,min(n,m)+1))
            for n in range(2*m+1)]


def quotient(u):
    out=[]
    for n in range(u+1):
        out.append(sub((comb(u,n),0),mul(Q,out[-1]) if n else ZERO))
    return out


def convolution(A,L):
    # The field coordinates can be signed: use direct addition, never
    # pass signed coefficient arrays into the nonnegative fastconv.
    out=[ZERO]*(len(A)+len(L)-1)
    for i,c in enumerate(L):
        for j,v in enumerate(A):out[i+j]=add(out[i+j],mul((c,0),v))
    return out


def minor(A,n):return sub(mul(A[n],A[n]),mul(A[n-1],A[n+1]))


def main():
    started=time.monotonic();rng=Random(20261029721);counts=Counter();sha=hashlib.sha256()
    for u in range(3,91):
        P=quotient(u)
        for n in range(u):
            direct=ZERO
            for j in range(n+1):
                direct=add(direct,mul((comb(u-1-j,n-j),0),power(sub(ONE,Q),j)))
            assert direct==P[n]
            counts['independent_positive_binomial_expansions']+=1
        assert P[-1]==power(sub(ONE,Q),u)
        for n in range(1,u):
            assert sign(sub(mul((n*(u-n),0),mul(P[n],P[n])),
                mul(((n+1)*(u-n+1),0),mul(P[n-1],P[n+1]))))>=0
            counts['exact_ULC_kernel_minors']+=1
        for s in range(2,u-1):
            for k in range(1,s+1):
                K=sub(mul(P[s],P[k]),mul(P[s+1],P[k-1]))
                T=add(add(P[k+1],mul(mul((2,0),Q),P[k])),mul(mul(Q,Q),P[k-1]))
                assert sign(sub(K,mul(power(Q,s),T)))>=0,('kernel',u,s,k)
                counts['exact_quantitative_all_read_kernel_budgets']+=1
        sha.update(json.dumps([u,P],separators=(',',':')).encode())
    for trial in range(1600):
        u=rng.randint(3,70);h=rng.randint(1,u-1);a=rng.randint(1,(u-1)//2)
        ratios=[a]+sorted([rng.randint(1,a) for _ in range(h-1)],reverse=True)
        L=[1]
        for v in ratios:L.append(L[-1]*v)
        B=convolution(quotient(u),L)
        for s in range(1,u-1):
            T=add(add(B[s+1],mul(mul((2,0),Q),B[s])),mul(mul(Q,Q),B[s-1]))
            assert sign(sub(minor(B,s),mul(power(Q,s),T)))>=0,('robust generic',u,L,s)
            counts['exact_generic_LC_numerator_robust_budgets']+=1
        counts['generic_LC_numerators']+=1
        sha.update(json.dumps([u,L,B],separators=(',',':')).encode())
    for trial in range(2400):
        V=rng.choices(range(3,25),k=rng.randint(1,9));h=sum(t-1 for t in V);m=h+rng.randint(0,12)
        L=[1]
        for t in V:L=fastconv(L,[1]*t)
        C=fastconv(L,binary(m));E=fastconv(L,[comb(m+1,k) for k in range(m+2)])
        a=evaluate(L,(0,-1));amp=mul(absolute(a),power(Q,m))
        assert sign(sub(ONE,amp))>=0
        counts['exact_entire_CI_amplitude_budgets']+=1
        B=[]
        for s in range(h+1):B.append(sub((E[s],0),mul(Q,B[-1]) if s else ZERO))
        b=[sub((0,C[n-1] if n else 0),(C[n],0)) for n in range(len(C))]
        for n in range(m+1,m+h+2):
            assert b[n]==sub(B[n-m-1],mul(a,power(PSI,n))),('deficit identity',V,m,n)
            assert sign(b[n])>0
            counts['independent_exact_geometric_deficit_identities']+=1
        for n in range(m+2,m+h+1):
            assert sign(minor(b,n))>=0,('deficit LC',V,m,n)
            counts['exact_LC_geometric_deficit_minors']+=1
        for n in range(m,len(C)-1):
            M=C[n]**2-C[n-1]*C[n+1]
            assert M>=0,('infinite padding LC',V,m,n)
            counts['exact_entire_infinite_padding_CI_tail_LC_minors']+=1
        for n in range(m+1,m+h):
            M=C[n]**2-C[n-1]*C[n+1];Mn=C[n+1]**2-C[n]*C[n+2]
            lhs=add(mul((C[n],0),minor(b,n+1)),mul(b[n],(Mn,0)))
            rhs=mul(mul(PHI,b[n+1]),(M,0))
            assert lhs==rhs
            counts['exact_backward_LC_transport_identities']+=1
        counts['actual_CI_infinite_padding_contexts']+=1
        sha.update(json.dumps([V,m,C,b],separators=(',',':')).encode())
        if trial%3==0:
            u=m+1;r=len(V);W=h+r;T=2*u+W
            alpha=(m+h+1)//2+1+rng.choice([0,1,2,h]);size=T+alpha+2
            F=arm_prefix(alpha,[2]*u+sorted(V),size)
            # The infinite earlier source depends on the tail order; use
            # exactly the same sorted actual word in both constructions.
            Finf=[1]*(size+1)
            for t in [2]*u+sorted(V):Finf=append_reference(Finf,t)
            Dinf=[0,0]+[max(0,Finf[n]-Finf[n-1]) for n in range(2,len(Finf))]
            D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            ell=D.index(max(D));ellinf=Dinf.index(max(Dinf));bound=r+2+(3*m+h+1)//2
            assert ell==ellinf and ell<=bound,('mode clamp',V,m,alpha,ell,ellinf,bound)
            assert D[:ell+1]==Dinf[:ell+1]
            for n in range(u+r+1,ell):
                assert D[n]**2>=D[n-1]*D[n+1]
                counts['exact_large_padding_pre_first_mode_LC_minors']+=1
            G=list(accumulate(F));best=1
            for N in range(4,T+2):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W+1:
                    assert G[best]*D[N-1]>=G[best-1]*D[N],('late actual C',V,m,alpha,N,best)
                    counts['exact_large_padding_actual_all_read_prefix_minimum_C_payments']+=1
                    counts['large_padding_logical_shift_coverage']+=N-3
            counts['actual_large_padding_mode_and_late_C_contexts']+=1
            sha.update(json.dumps([alpha,F,D,ell],separators=(',',':')).encode())
    out=dict(status='PASS_EXACT_QA_WRITTEN_UNBOUNDED_INFINITE_PADDING_CI_ENTRANCE',
        counts=dict(counts),state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='Exact finite QA of the written unbounded proof and specified large-padding corollary. At the single entrance only alpha<=h remains unhandled here. Generic two-seed closure, general C, A2 and original UI remain OPEN.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
