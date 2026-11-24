"""Explore exact finite owner states left by the generic source-curvature payment.

The generic CI test is a proved sufficient comparison, not equality with
actual coefficients. Any failed payment is an auxiliary obstruction only.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
from collections import Counter
from hashlib import sha256
import json,time
from audit_joint_structure import arm

ROOT=Path(__file__).resolve().parent


def partitions(n,lower=1):
    if n==0:
        yield ()
        return
    for v in range(lower,n+1):
        for tail in partitions(n-v,v):yield (v,)+tail


def main():
    start=time.monotonic();counts=Counter();remaining=[];states=[];witness=None;digest=sha256()
    at=lambda A,i:A[i] if 0<=i<len(A) else 0
    for alpha in (1,2):
        kappa=9;d=kappa-alpha;maxD=min(2*d*(d-3),12*d-25)
        for e in range(d-2):
            L=d-e-3
            for r in range(maxD//2+1):
                D=2*r+2+e
                if D<6 or D>maxD:continue
                lower=Fraction(0)
                if L<0:continue
                for t in [0]+list(range(2,kappa-2)):
                    m=L+t
                    if r<m:continue
                    w=1 if t==0 else 2**(t-2)
                    lower+=w*Fraction(comb(r,m),comb(r+e+m+2,m))
                if lower>=Fraction(e+1,r+1):
                    counts['all_owner_CI_paid_rank_states']+=1
                    continue
                states.append((alpha,r,e,D))
        for al,r,e,D in states:
            if al!=alpha:continue
            layer=Counter()
            for inc in partitions(D):
                h=len(inc)
                if h<6 or inc[0]>alpha:continue
                U=[x+1 for x in inc];A=arm(alpha,U);q=A[::-1]
                old=max(0,at(q,r)-at(q,r-1));new=max(0,at(q,r+1)-at(q,r));C=new-old
                counts['complete_owners_examined']+=1;layer['owners']+=1
                if C<=0:continue
                counts['strict_primitive_curvature_owners']+=1;layer['critical']+=1
                b0=D-r+h+1-d
                payment=at(A,b0)+sum(2**(t-2)*at(A,b0-t) for t in range(2,kappa-2))
                digest.update(json.dumps([alpha,r,e,inc,C,payment],separators=(',',':')).encode())
                if payment<C:
                    witness=dict(alpha=alpha,U=U,h=h,r=r,e=e,D=D,kappa=9,birth_index=b0,
                        primitive_curvature=C,guaranteed_source_payment=payment)
                    break
            remaining.append(dict(alpha=alpha,r=r,e=e,D=D,counts=dict(layer)))
            if witness:break
        if witness:break
    out=dict(status='EXACT_KAPPA_NINE_SOURCE_PAYMENT_OBSTRUCTION' if witness else 'PASS_KAPPA_NINE_GENERIC_AND_FINITE_OWNER_PAYMENT',
        counts=dict(counts),generic_unpaid_rank_states=states,layers=remaining,witness=witness,
        canonical_critical_sha256=digest.hexdigest(),seconds=time.monotonic()-start,
        scope='CanonicalalphaStar1/2only,ownerh>=6,kappaY9;h>=4gap6theorempaysalphaStar>=3. GenericCIcurvatureandgenuineEARLYsourcew>=2^(t-2)reducefiniteownercomplement. FullpositiveTrequiresD<=min(2d(d-3),12d-25). A PASS needsINDEPENDENTexhaustivecoverage/unboundedjoiningbeforetheoremclaim;obstructionrejectsONLYthissourcepayment,notS/C/A2/originalUI.')
    (ROOT/'probe_kappa_nine_source_complement.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
