"""Full initial-atom primitive and complete low-degree correction exact QA."""
from pathlib import Path
from random import Random
from collections import Counter
import json,time,hashlib
from probe_tribonacci_quadratic_inverse import ZERO,ONE,A,B,add,sub,mul,power,sign,pc
from build_tribonacci_rich_reverse_certificate import reverse
ROOT=Path(__file__).resolve().parent
L=(0,1,0);S=(1,2,-1)
def pc_field_int(J,K):
    out=[ZERO]*(len(J)+len(K)-1)
    for n,v in enumerate(J):
        for k,c in enumerate(K):out[n+k]=add(out[n+k],tuple(c*x for x in v))
    return out
def main():
    start=time.monotonic();rng=Random(20261031743);ct=Counter();sha=hashlib.sha256()
    cases=[(u,rng.randint(2*u,2*u+60)) for u in [rng.randint(4,100) for _ in range(350)]]
    for _ in range(200):
        u=rng.randint(0,140);r=rng.randint(18,150);N=mul(power(S,u),power(B,r+1))
        if sign(sub(ONE,tuple(64*x for x in N)))>=0:cases.append((u,r))
    for u,r in cases:
        E=[1]
        for t in [2]*u+[3]*r:E=pc(E,[1]*t)
        J=reverse(E);d=[]
        for n,v in enumerate(J):
            t=sub(v,J[n-1] if n else ZERO);d.append(t if sign(t)>0 else ZERO)
        assert d[0]==J[0]
        for n in range(1,len(d)-1):
            assert sign(sub(mul(d[n],d[n]),mul(d[n-1],d[n+1])))>=0,(u,r,n)
            ct['FULL_positive_primitive_LC_minors_including_initial_atom']+=1
        R0=sub(ONE,J[0]);R1=sub(sub((u+r,0,0),mul(A,J[0])),J[1])
        for K in [[1,1],[1,1,1]]:
            NJ=reverse(pc(E,K));C=pc_field_int(J,K)
            if len(K)==2:C[0]=add(C[0],mul(L,R1))
            else:
                C[0]=add(C[0],mul(L,sub(add(R0,R1),mul(A,mul(L,R1)))))
                C[1]=add(C[1],mul(L,R1))
            assert NJ==C
            ct['COMPLETE_binary_or_ternary_quotient_correction_hosts']+=1
            ct['ALL_quotient_correction_coefficient_reads']+=len(C)
        ct['actual_proper_quotient_hosts']+=1
        sha.update(str((u,r,J[:5],d[:5])).encode())
    out=dict(status='EXACT_QA_PASS_FULL_TRIBONACCI_QUOTIENT_POSITIVE_PRIMITIVE_UNDER_PROOF_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      scope='QAONLY;fullwrittenunboundednorm-cone/windowclosure+complete31base/235head-coefficientcertificateproveFULLprimitiveLCincludingrank0. NOTwholeactuallambda-residualprimitive(whichisFALSE). OriginalUIstillOPEN.')
    (ROOT/'audit_tribonacci_quotient_primitive.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
