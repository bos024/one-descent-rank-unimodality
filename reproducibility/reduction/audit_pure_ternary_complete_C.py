"""Exact actual-host QA and actual quotient/future-tail identification."""
from pathlib import Path
from collections import Counter
from itertools import accumulate
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import c_minimum
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,mul,add,sub,sign
LAM=(0,1,0)
def scale(v,c):return tuple(c*x for x in v)
def pure_product(r):
    E=[1]
    for _ in range(r):
        E=[sum(E[j] for j in range(max(0,n-2),min(n,len(E)-1)+1)) for n in range(len(E)+2)]
    return E
def quotient(E):
    D=len(E)-1;J=[ZERO]*(D-1)
    for n in range(D,1,-1):
        v=scale(ONE,E[n])
        if n<len(J):v=sub(v,J[n])
        if n-1<len(J):v=sub(v,mul(A,J[n-1]))
        J[n-2]=mul(LAM,v)
    return J
def infinite_derivative(r):
    d=[1,1]
    for _ in range(1,r):
        nxt=[1,1]+[0]*(len(d)+1)
        for n,v in enumerate(d):
            for s in [1,2,3]:nxt[n+s]+=v
        d=nxt
    return d
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(20261101018)
    for r in [18,19,20,24,35,50,80]:
        E=pure_product(r);J=quotient(E);d=infinite_derivative(r);H=len(J)-1;X={H:ZERO}
        for n in range(H-1,-2,-1):X[n]=mul(B,add(X[n+1],J[n+1] if n+1>=0 else ZERO))
        for s in range(H+1):
            y=add(X.get(s,ZERO),X[s-1]);expected=scale(ONE,d[r+s] if r+s<len(d) else 0)
            assert y==expected,(r,s)
            ct['exact_ACTUAL_infinite_derivative_future_quotient_identity_reads']+=1
        sha.update(str((r,E,J,d)).encode())
    cases=[(r,a) for r in range(18,45) for a in [1,2,3,4,5,r,2*r]]
    cases +=[(rng.randint(18,150),rng.randint(1,350)) for _ in range(300)]
    for r,alpha in cases:
        F=arm_prefix(alpha,[3]*r,alpha+3*r+1);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
        L=D.index(max(D));A0=r+2
        assert L<=2*r
        for n in range(A0,L):assert D[n]**2>=D[n-1]*D[n+1];ct['actual_PREmode_D_LC_minors_from_FIRST_physical_source']+=1
        if A0+1<=L:
            gap=(-D[A0+1]-(r-4),D[A0],0);assert sign(gap)>=0
            assert F[A0-1]*D[A0]>=F[A0-2]*D[A0+1]
            ct['actual_growth_gap_and_TRUE_ordinary_entry_seed']+=1
        c_minimum(F,D,4,L,ct)
        ct['actual_unbounded_family_QA_hosts']+=1;sha.update(str((r,alpha,F,D,L)).encode())
    out=dict(status='EXACT_QA_PASS_PURE_TERNARY_COMPLETE_C_UNDER_PROOF_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QAONLY;unboundedr>=18proofusesnewgeneralcut+registeredproperquotientprimitive+FIRSTphysicalboundary+TRUEordinaryentry. Smallrcompletefinitepremiseseparate. NoactualgeneralC/UIclaim.')
    (ROOT/'audit_pure_ternary_complete_C.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
