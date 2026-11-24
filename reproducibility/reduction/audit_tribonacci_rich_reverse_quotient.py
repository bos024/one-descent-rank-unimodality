"""Exact QA of the proper quotient, complete remainder and terminal norm cone."""
from pathlib import Path
from random import Random
from collections import Counter
import json,time,hashlib
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,add,sub,mul,power,sign,pc
from build_tribonacci_rich_reverse_certificate import reverse
ROOT=Path(__file__).resolve().parent
L=(0,1,0);S=(1,2,-1)
def scale(v,k):return tuple(k*x for x in v)
def main():
    start=time.monotonic();rng=Random(20261031739);ct=Counter();sha=hashlib.sha256()
    cases=[(u,r,'rich') for u in range(4,13) for r in range(2*u,2*u+8)]
    cases +=[(u,rng.randint(2*u,2*u+70),'rich') for u in [rng.randint(4,100) for _ in range(250)]]
    for _ in range(250):
        u=rng.randint(0,140);r=rng.randint(18,160);norm=mul(power(S,u),power(B,r+1))
        if sign(sub(ONE,scale(norm,64)))>=0:cases.append((u,r,'general_norm_cone'))
    for u,r,kind in cases:
        E=[1]
        for t in [2]*u+[3]*r:E=pc(E,[1]*t)
        J=reverse(E);assert all(sign(v)>0 for v in J),(u,r)
        for n in range(1,len(J)-1):
            assert sign(sub(mul(J[n],J[n]),mul(J[n-1],J[n+1])))>=0,(u,r,n)
            ct['whole_proper_quotient_LC_minors']+=1
        R0=sub(ONE,J[0]);R1=sub(sub((u+r,0,0),mul(A,J[0])),J[1])
        for n,e in enumerate(E):
            v=J[n] if n<len(J) else ZERO
            if 0<=n-1<len(J):v=add(v,mul(A,J[n-1]))
            if 0<=n-2<len(J):v=add(v,mul(B,J[n-2]))
            if n==0:v=add(v,R0)
            if n==1:v=add(v,R1)
            assert v==(e,0,0)
            ct['ALL_polynomial_division_identity_reads']+=1
        norm=add(sub(mul(B,mul(R0,R0)),mul(A,mul(R0,R1))),mul(R1,R1))
        assert norm==mul(power(S,u),power(B,r+1))
        assert sign(sub(ONE,scale(norm,64)))>=0
        for v in [R0,R1]:assert sign(add(ONE,scale(v,4)))>=0 and sign(sub(ONE,scale(v,4)))>=0
        ct['EXACT_norm_and_complete_remainder_box_hosts']+=1;ct[kind+'_hosts']+=1
        sha.update(str((u,r,R0,R1,J[:4])).encode())
    out=dict(status='EXACT_QA_PASS_PROPER_TRIBONACCI_RICH_QUOTIENT_UNDER_PROOF_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='QAONLY. WrittenONEpureentrance+30smallrcontexts+unboundedterminalnormcone/completeBernsteincornersproveALLrichu>=4,r>=2uGLOBALordinaryLCpositivePOLYNOMIALquotient. PrimitiveLCandactualDtransferNOTasserted.')
    (ROOT/'audit_tribonacci_rich_reverse_quotient.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
