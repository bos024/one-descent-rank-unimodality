"""Diagnostic only: weaker ordinary-LC route to complete C in the rich cone."""
from pathlib import Path
from random import Random
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from probe_tribonacci_quadratic_inverse import sign
def main():
    st=time.monotonic();ct=Counter();bad={};sha=hashlib.sha256();rng=Random(2026110124)
    cases=[(u,r,a) for u in range(1,34) for r in [max(8,2*u),max(12,3*u),max(18,4*u)] for a in [1,2,3,4,u+r,2*u+3*r]]
    cases +=[(u,2*u+rng.randrange(0,4*u+1),rng.randint(1,5*u)) for u in [rng.randint(34,150) for _ in range(800)]]
    for u,r,alpha in cases:
        F=arm_prefix(alpha,[2]*u+[3]*r,alpha+2*u+3*r);D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];M=D.index(max(D));A=r+3
        assert sign((-F[A],F[A-1],0))>=0
        for n in range(A,len(F)-1):
            v=F[n]**2-F[n-1]*F[n+1];ct['ENTIRE_ordinary_tail_LC_minors']+=1
            if n<M:ct['pre_FIRSTDmode_ordinary_LC_minors']+=1
            if v<0 and ('premode' if n<M else 'postmode') not in bad:
                bad['premode' if n<M else 'postmode']=dict(u=u,r=r,alpha=alpha,n=n,M=M,minor=v,triple=F[n-1:n+2])
        ct['actual_hosts']+=1;sha.update(str((u,r,alpha,F,D,M)).encode())
    out=dict(status='DIAGNOSTIC_ONLY_RICH_TERNARY_ORDINARY_LC_ROUTE',counts=dict(ct),counterexamples=bad,state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='NOanalyticordinaryLCproofasserted;IFordinaryFLCfromFIRSTordinarysourceA=r+3throughFIRSTDmode-1andprotectedentryF_A/Fprev<=lambdaTHENFULLCwithoutstrongDminor. No actualCDFLCassumed.')
    (ROOT/'probe_rich_ternary_ordinary_tail.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
