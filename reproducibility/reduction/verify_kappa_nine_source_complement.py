"""Independent reverse-polynomial and maximum-part partition reconstruction."""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from collections import Counter
from hashlib import sha256
import json,time

ROOT=Path(__file__).resolve().parent


@lru_cache(None)
def bounded_parts(total,maximum):
    if total==0:return ((),)
    rows=[]
    for largest in range(min(total,maximum),0,-1):
        for rest in bounded_parts(total-largest,largest):rows.append(rest+(largest,))
    return tuple(rows)


def reverse_arm(alpha,U):
    q=[1]*(alpha+1);weight=alpha
    for t in U:
        out=[0]*(len(q)+t)
        for i,v in enumerate(q):
            for s in range(t):out[i+s]+=v
        weight+=t;out[weight]+=1;q=out
    return q


def main():
    start=time.monotonic();raw=(ROOT/'probe_kappa_nine_source_complement.json').read_bytes();producer=json.loads(raw)
    assert producer['status']=='PASS_KAPPA_NINE_GENERIC_AND_FINITE_OWNER_PAYMENT'
    counts=Counter();states=[];layers=[];digest=sha256()
    at=lambda A,i:A[i] if 0<=i<len(A) else 0
    for alpha in (1,2):
        d=9-alpha;maxD=min(2*d*(d-3),12*d-25)
        for e in range(d-2):
            L=d-e-3
            for r in range(maxD//2+1):
                D=2*r+2+e
                if D<6 or D>maxD:continue
                lower=Fraction(0)
                for t in [0]+list(range(2,7)):
                    m=L+t
                    if r<m:continue
                    step=Fraction(1)
                    for i in range(m):step*=Fraction(r-i,r+e+3+i)
                    lower+=(1 if t==0 else 2**(t-2))*step
                if lower>=Fraction(e+1,r+1):
                    counts['all_owner_CI_paid_rank_states']+=1
                else:states.append((alpha,r,e,D))
        for al,r,e,D in states:
            if al!=alpha:continue
            layer=Counter()
            for inc in sorted(bounded_parts(D,D)):
                h=len(inc)
                if h<6 or inc[0]>alpha:continue
                q=reverse_arm(alpha,[x+1 for x in inc]);a=len(q)-1
                C=max(0,at(q,r+1)-at(q,r))-max(0,at(q,r)-at(q,r-1))
                counts['complete_owners_examined']+=1;layer['owners']+=1
                if C<=0:continue
                counts['strict_primitive_curvature_owners']+=1;layer['critical']+=1
                b0=D-r+h+1-d
                F=lambda index:at(q,a-index) if index>=0 else 0
                payment=F(b0)+sum(2**(t-2)*F(b0-t) for t in range(2,7))
                assert payment>=C,(alpha,inc,r,e,C,payment)
                digest.update(json.dumps([alpha,r,e,inc,C,payment],separators=(',',':')).encode())
            layers.append(dict(alpha=alpha,r=r,e=e,D=D,counts=dict(layer)))
    assert states==[tuple(row) for row in producer['generic_unpaid_rank_states']]
    assert dict(counts)==producer['counts'] and layers==producer['layers']
    assert digest.hexdigest()==producer['canonical_critical_sha256']
    sharp=[]
    for g in (12,15,20):
        A=reverse_arm(1,[2]*6);B=reverse_arm(1,[9]*g)
        P=[0]*(len(A)+len(B)-1)
        for i,v in enumerate(A):
            for j,w in enumerate(B):P[i+j]+=v*w
        n=len(P)-1-12
        current=2*P[n]-P[n-1];upper=2*P[n+1]-P[n]
        assert (current,upper)==(17,19),(g,current,upper)
        H=2*P[2]-3*P[1]+P[0]
        assert H>=3
        sharp.append(dict(alpha=1,U=[2]*6,beta=1,V_capacity=9,V_count=g,j=12,
            kappaY=10,tail=current,next_tail=upper,head1_budget=H))
    out=dict(status='PASS_INDEPENDENT_KAPPA_NINE_HSIX_COMPLETE_OWNER_COMPLEMENT',counts=dict(counts),
        canonical_critical_sha256=digest.hexdigest(),certificate_sha256=sha256(raw).hexdigest(),
        generic_unpaid_rank_states=len(states),all_layer_count=len(layers),
        sharp_kappa_ten_actual_profiles=sharp,seconds=time.monotonic()-start,
        scope='ALLcanonicalalpha1/2,h>=6sourcegapstatesafterPROVEDunboundedquadratic/linearreduction;244CIpaidstatesand13544finiteowners/2464criticalexactlyreconstructedbyINDEPENDENTindividualratios/reversepolynomials/maxpartpartitions. kappa9NONRECOVERYtheoremneedswrittenjoining;threshold9SHARPforh>=6byactualkappa10tail17to19,Sheadpays. NooriginalUIclaim.')
    (ROOT/'verify_kappa_nine_source_complement.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
