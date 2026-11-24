"""Exact QA of the new full-count quadratic inverse theorem, not its proof."""
from pathlib import Path
from random import Random
from collections import Counter
import json,time,hashlib
from probe_tribonacci_quadratic_inverse import pc,inverse,sub,add,mul,power,sign,terminal_norm,A,ONE,ZERO
ROOT=Path(__file__).resolve().parent
def scale(x,k):return tuple(k*a for a in x)
def main():
    started=time.monotonic();rng=Random(20261031731);ct=Counter();sha=hashlib.sha256()
    hosts=[(u,r) for u in range(22) for r in range(22) if u+r]+[(rng.randint(0,160),rng.randint(0,160)) for _ in range(400)]
    for u,r in hosts:
        if not u+r:continue
        E=[1]
        for t in [2]*u+[3]*r:E=pc(E,[1]*t)
        f=inverse(E);p=f[:-2];ms=[sub(mul(p[n],p[n]),mul(p[n-1],p[n+1])) for n in range(1,len(p)-1)]
        if (u,r)==(0,2):
            assert ms==[(2,-3,1)] and sign(ms[0])<0;ct['exact_single_exception_controls']+=1
        else:
            assert all(sign(v)>0 for v in p) and all(sign(v)>=0 for v in ms),(u,r)
            ct['positive_LC_prefix_hosts']+=1;ct['retained_coefficient_reads']+=len(p);ct['LC_minor_reads']+=len(ms)
        expected=mul(power(A,2*u),power(sub(ONE,A),r));assert terminal_norm(f)==expected
        ct['exact_full_two_count_terminal_norm_identities']+=1
        if u+r>=18:
            for v in f[-2:]:assert sign(add(scale(v,4),ONE))>=0 and sign(sub(ONE,scale(v,4)))>=0
            ct['uniform_terminal_quarter_box_hosts']+=1
        sha.update(str((u,r,f[-2:],p[:4])).encode())
    out=dict(status='EXACT_QA_PASS_FULL_COUNT_TRIBONACCI_QUADRATIC_INVERSE_UNDER_PROOF_AUDIT',counts=dict(ct),
      state_sha256=sha.hexdigest(),seconds=time.monotonic()-started,
      scope='QAONLY:writtenunboundedtwo-countnorm+complete188entrance/125Bernsteincoefficientproof. PositiveGLOBALordinaryLCtruncatedthroughD-2exceptu0r2. LastTWOactualquotientcoefficientsNOTassertedpositive. ActualcompositionC/A2/originalUIstillOPEN.')
    (ROOT/'audit_tribonacci_quadratic_inverse.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
