"""Exact positive C/(1+qz) residual QA plus full reference/actual C checks."""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_homogeneous_reference_and_sharp_entrance import c_minimum
from audit_arbitrary_Fibonacci_tail_late_C import mul,sub,sign,power
def reference(r,N):
    F=[1]
    for n in range(1,N+1):F.append(F[-1]+(F[-2] if n>1 else 0))
    for _ in range(r):F=[1]+[sum(F[max(0,n-3):n]) for n in range(1,N+1)]
    return F
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(2026110144)
    for r in range(6,151):
        F=reference(r,6*r+3);H=[(v,-F[n-1] if n else 0) for n,v in enumerate(F)]
        assert H[3*r]==power((4,-2),r)
        for n in range(r+3,3*r):
            m=sub(mul(H[n],H[n]),mul(H[n-1],H[n+1]));assert sign(m)>=0
            ct['exact_golden_residual_LC_tail_minors']+=1
        for n in range(r+3,3*r+1):assert F[n]**2>=F[n-1]*F[n+1];ct['exact_reference_ordinary_LC_head_minors']+=1
        assert F[3*r+1]**2<F[3*r]*F[3*r+2];ct['exact_reference_FIRST_late_ordinary_LC_failure_controls']+=1
        D=[0,0]+[F[n]-F[n-1] for n in range(2,len(F))];assert all(v>=0 for v in D)
        c_minimum(F,D,4,6*r,ct);ct['infinite_binary_stationary_three_reference_hosts']+=1;sha.update(str((r,F,H[3*r-2:3*r+2])).encode())
    cases=[(r,u,a) for r in range(6,35) for u in [2*r-3,2*r-2,2*r,3*r] for a in [1,2,u+r]]
    cases +=[(r,2*r-3+rng.randint(0,3*r),rng.randint(1,300)) for r in [rng.randint(6,100) for _ in range(200)]]
    for r,u,alpha in cases:
        F=arm_prefix(alpha,[2]*u+[3]*r,alpha+2*u+3*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];L=D.index(max(D))
        c_minimum(F,D,4,L,ct);ct['actual_binary_dense_complete_C_hosts']+=1;sha.update(str((r,u,alpha,F,D,L)).encode())
    out=dict(status='EXACT_QA_PASS_ALL_STATIONARY_THREE_REFERENCE_AND_BINARY_DENSE_ACTUAL_C_UNDER_PROOF_AUDIT',counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='QAONLY. AnalyticreferenceHLCr>=6withONEfixedr6base+twoleftminors+oldCIterminalbudget;ordinaryreferenceLCONLYA..W/fullCviaoldlateC. Actualallr/u>=max(0,2r-3)viareferenceprefix+universallateC. GeneraloriginalUIOPEN.')
    (ROOT/'audit_stationary_ternary_reference_C.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
