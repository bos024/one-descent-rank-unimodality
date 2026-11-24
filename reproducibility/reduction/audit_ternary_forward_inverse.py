"""Exact QA of unbounded written forward-inverse and diagonal identities."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,power,sign,evaluate
from audit_minimum_staircase_scaled_dyadic import arm_prefix
Q=(-1,1);ZERO=(0,0);PHI=(0,1)
def pc(a,b,N=None):
    n=len(a)+len(b)-1 if N is None else N+1
    c=[0]*n
    for i,x in enumerate(a):
        for j,y in enumerate(b[:max(0,n-i)]):c[i+j]+=x*y
    return c
def kernel(u,r):
    E=[1]
    for t in [2]*u+[3]*r:E=pc(E,[1]*t)
    return E
def forward(E):
    a=[];prev=ZERO
    for e in E:prev=sub((e,0),mul(Q,prev));a.append(prev)
    return a
def main():
    started=time.monotonic();rng=Random(20261031712);ct=Counter();sha=hashlib.sha256()
    hosts=[(u,r) for u in range(21) for r in range(41)]+[(rng.randint(1,160),rng.randint(0,160)) for _ in range(200)]
    controls=[]
    for u,r in hosts:
        E=kernel(u,r);a=forward(E);tau=power((2,-1),u);tau=mul(tau,power((4,-2),r))
        assert a[-1]==tau==evaluate(E,(1,-1));assert all(sign(x)>0 for x in a)
        margins=[sub(mul(a[n],a[n]),mul(a[n-1],a[n+1])) for n in range(1,len(a)-1)]
        if u or r>=6:
            assert all(sign(x)>=0 for x in margins),(u,r)
            budget=sub((1,1),mul((-2*r-2*u,2+2*r+2*u),tau))
            assert sign(budget)>=0
            ct['positive_LC_truncated_forward_inverse_hosts']+=1;ct['exact_LC_minors']+=len(margins)
        elif r:
            assert sign(margins[-1])<0
            if r<=5:controls.append(dict(r=r,penultimate_minor=margins[-1]))
        sha.update(str((u,r,a[-1],margins[-1:] if margins else [])).encode())
    S2=[0,1,1];S3=[0,1,1,1];K=pc(S2,pc(S3,S3))
    for _ in range(300):
        u=rng.randint(0,35);r=rng.randint(0,50);alpha=rng.randint(1,60)
        N=alpha+2*(u+1)+3*(r+2)+3
        old=arm_prefix(alpha,[2]*u+[3]*r,N);new=arm_prefix(alpha,[2]*(u+1)+[3]*(r+2),N)
        B=[0]*(N+1);P=[1]
        for j in range(r):
            for n,x in enumerate(P):B[n]+=x
            P=pc(P,S3,N)
        companion=[0]*(N+1);companion[0]=1
        for A in [S3,pc(S3,S3),[0,0,0]+pc(pc(S3,S3),B,N)]:
            for n,x in enumerate(A[:N+1]):companion[n]+=x
        rhs=pc(K,old,N)
        assert new==[x+y for x,y in zip(rhs,companion)]
        H=[1]
        for n in range(1,N+1):H.append(sum(H[max(0,n-3):n]))
        E=[x-y for x,y in zip(H,old)];En=[x-y for x,y in zip(H,new)]
        src=pc([0,0,0]+pc(P,pc(S3,S3),N),H,N)
        assert En==[x+y for x,y in zip(pc(K,E,N),src)]
        L=[E[n+2]-E[n+1] for n in range(N-1)];Ln=[En[n+2]-En[n+1] for n in range(N-1)]
        d3=pc([1,1],H,N)
        Bnew=pc(P,pc(S3,S3),N);ls=pc([0,1],Bnew,N-2)
        source2=pc([0,0,0]+Bnew,d3,N-2)
        assert Ln==[x+y+z for x,y,z in zip(pc(K,L,N-2),ls,source2)]
        ct['actual_ALL_coefficient_diagonal_companion_hosts']+=1
        ct['actual_companion_defect_and_derivative_identity_reads']+=3*(N-1)
        sha.update(str((alpha,u,r,new[-8:])).encode())
    out=dict(status='EXACT_QA_TERNARY_FORWARD_INVERSE_AND_POSITIVE_DIAGONAL_IDENTITIES',counts=dict(ct),pure_small_controls=controls,
        state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
        scope='QA ONLY. Written analytic induction proves ALLu>=1/r>=0 and pure r>=6 truncated forward inverse LC. No actual full-C diagonal u>=33 or originalUI claim.')
    (ROOT/'audit_ternary_forward_inverse.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
