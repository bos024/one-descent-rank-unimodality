"""Explore uniform gap EIGHT for h>=6, with ALL initial runs by exact clamp.

A pass requires independent reconstruction and written unbounded joining.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
from collections import Counter
from hashlib import sha256
import json,time,sys
from audit_joint_structure import arm
from probe_kappa_nine_source_complement import partitions

ROOT=Path(__file__).resolve().parent


def main():
    start=time.monotonic();d=7 if '--gap-seven' in sys.argv else 8
    alpha_min=2 if d==7 else 1;maxD=min(2*d*(d-3),12*d-25)
    counts=Counter();states=[];layers=[];digest=sha256();witness=None
    at=lambda A,i:A[i] if 0<=i<len(A) else 0
    for e in range(d-2):
        L=d-e-3
        for r in range(maxD//2+1):
            D=2*r+2+e
            if D<6 or D>maxD:continue
            low=Fraction(0)
            for t in [0]+list(range(2,7)):
                m=L+t
                if r<m:continue
                low+=(1 if t==0 else 2**(t-2))*Fraction(comb(r,m),comb(r+e+m+2,m))
            if low>=Fraction(e+1,r+1):counts['generic_CI_paid_rank_states']+=1
            else:states.append((r,e,D))
    for r,e,D in states:
        layer=Counter()
        for inc in partitions(D):
            h=len(inc)
            if h<6:continue
            U=[x+1 for x in inc];b0=D-r+h+1-d;N=max(b0,r+1)
            for alpha in range(alpha_min,max(N,alpha_min)+1):
                A=arm(alpha,U);q=A[::-1]
                C=max(0,at(q,r+1)-at(q,r))-max(0,at(q,r)-at(q,r-1))
                counts['complete_initial_clamped_owners']+=1;layer['owners']+=1
                if C<=0:continue
                payment=at(A,b0)+sum(2**(t-2)*at(A,b0-t) for t in range(2,7))
                counts['strict_primitive_curvature_states']+=1;layer['critical']+=1
                digest.update(json.dumps([r,e,inc,alpha,C,payment],separators=(',',':')).encode())
                if payment<C:
                    witness=dict(alpha=alpha,U=U,h=h,r=r,e=e,D=D,d=d,C=C,payment=payment,b0=b0)
                    break
            if witness:break
        layers.append(dict(r=r,e=e,D=D,counts=dict(layer)))
        if witness:break
    out=dict(status=f'EXACT_GAP_{d}_HSIX_SOURCE_PAYMENT_OBSTRUCTION' if witness else f'PASS_GAP_{d}_HSIX_COMPLETE_SOURCE_PAYMENT',
        gap=d,alpha_min=alpha_min,
        counts=dict(counts),generic_unpaid_rank_states=states,layers=layers,witness=witness,
        canonical_critical_sha256=digest.hexdigest(),seconds=time.monotonic()-start,
        scope='CandidateUNIFORMgap8ownerh>=6,ALLalpha/capacitiesviaPROVEDlinear/quadraticDandinitialrunclamp. Gap7runsalpha>=2(remainingalpha1kappa8alreadyPROVED);gap8runsALLalpha>=1. Minimumkappa>=9givescommonw0/w2..6profile. PASSneedsindependentfullfinitecoverageandwrittenunboundedjoiningbeforetheoremclaim. SourcepaymentobstructionNOTS/C/A2/originalUIcounter.')
    name='probe_gap_seven_hsix_source_complement.json' if d==7 else 'probe_gap_eight_hsix_source_complement.json'
    (ROOT/name).write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('layers','generic_unpaid_rank_states')}),flush=True)


if __name__=='__main__':main()
