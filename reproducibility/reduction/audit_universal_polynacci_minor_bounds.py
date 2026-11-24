"""Exact QA only for the universal sharp ordinary/golden-residual minor bounds."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_ternary_forward_inverse import qa,qm,qs,sub
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();C=(2,1);c=(1,-1)
    for t in list(range(2,81))+[100,150,250,500]:
        N=2000 if t<=80 else 3*t+20;h=[1];window=1
        for n in range(1,N+2):
            h.append(window);window+=h[-1]
            if n>=t:window-=h[n-t]
        K=[(h[n]-(h[n-1] if n else 0),-(h[n-1] if n else 0)) for n in range(len(h))]
        assert h[t]**2-h[t-1]*h[t+1]==h[t-1]
        for n in range(1,N+1):
            m=h[n]**2-h[n-1]*h[n+1];assert abs(m)<=h[n-1]
            ct['ALLorder_ordinary_absolute_minor_reads']+=1
            if t>=3 and n>=3:
                assert qs(K[n-1])>0
                k=sub(qm(K[n],K[n]),qm(K[n-1],K[n+1]));bound=qm(C,K[n-1])
                assert qs(sub(bound,k))>=0 and qs(qa(bound,k))>=0
                ct['ALLorder_golden_residual_SHARP_constant_minor_reads']+=1
        if t>=3:
            m=sub(qm(K[t+1],K[t+1]),qm(K[t],K[t+2]))
            assert m==sub((1,0),qm(C,K[t]))
            assert K[t]==tuple((2**(t-2))*x for x in c)
            ct['EXACTsharp_boundary_formula_orders']+=1
        sha.update(str((t,h[-4:],K[t],K[t+1])).encode())
    out=dict(status='EXACT_QA_PASS_UNIVERSAL_SHARP_POLYNACCI_AND_GOLDEN_RESIDUAL_MINOR_ENVELOPES',
      counts=dict(ct),state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      scope='UniversalallorderproofusespositiveprobabilityquadratictransportandCOMPLETEsymbolicbands,NOTfiniteQA. Ordinaryconstant1attainedn=t;goldenconstantphi2optimalasn=t1,t->infty. NOgeneralC/A2/originalUIclaim.')
    (ROOT/'audit_universal_polynacci_minor_bounds.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
