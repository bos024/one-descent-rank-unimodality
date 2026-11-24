"""Independent COMPLETE gap7/gap8 alpha-clamped finite owner reconstruction."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
from hashlib import sha256
import json,time
from verify_kappa_nine_source_complement import bounded_parts,reverse_arm

ROOT=Path(__file__).resolve().parent


def verify(gap,alpha_min,name):
    raw=(ROOT/name).read_bytes();source=json.loads(raw)
    assert source['status']==f'PASS_GAP_{gap}_HSIX_COMPLETE_SOURCE_PAYMENT'
    counts=Counter();states=[];layers=[];digest=sha256()
    d=gap;maxD=min(2*d*(d-3),12*d-25);at=lambda A,i:A[i] if 0<=i<len(A) else 0
    for e in range(d-2):
        L=d-e-3
        for r in range(maxD//2+1):
            D=2*r+2+e
            if D<6 or D>maxD:continue
            low=Fraction(0)
            for t in (0,2,3,4,5,6):
                m=L+t
                if r<m:continue
                x=Fraction(1)
                for i in range(m):x*=Fraction(r-i,r+e+3+i)
                low+=(1 if t==0 else 2**(t-2))*x
            if low>=Fraction(e+1,r+1):counts['generic_CI_paid_rank_states']+=1
            else:states.append((r,e,D))
    for r,e,D in states:
        layer=Counter()
        for inc in sorted(bounded_parts(D,D)):
            h=len(inc)
            if h<6:continue
            b0=D-r+h+1-d;N=max(b0,r+1)
            for alpha in range(alpha_min,max(alpha_min,N)+1):
                q=reverse_arm(alpha,[x+1 for x in inc]);a=len(q)-1
                C=max(0,at(q,r+1)-at(q,r))-max(0,at(q,r)-at(q,r-1))
                counts['complete_initial_clamped_owners']+=1;layer['owners']+=1
                if C<=0:continue
                F=lambda index:at(q,a-index) if index>=0 else 0
                payment=F(b0)+sum(2**(t-2)*F(b0-t) for t in range(2,7))
                assert payment>=C,(gap,alpha,inc,r,e,C,payment)
                counts['strict_primitive_curvature_states']+=1;layer['critical']+=1
                digest.update(json.dumps([r,e,inc,alpha,C,payment],separators=(',',':')).encode())
        layers.append(dict(r=r,e=e,D=D,counts=dict(layer)))
    assert [list(s) for s in states]==source['generic_unpaid_rank_states']
    assert layers==source['layers'] and dict(counts)==source['counts']
    assert digest.hexdigest()==source['canonical_critical_sha256']
    return dict(gap=gap,alpha_min=alpha_min,counts=dict(counts),layers=len(layers),
        canonical_critical_sha256=digest.hexdigest(),certificate_sha256=sha256(raw).hexdigest())


def main():
    start=time.monotonic()
    configs=[verify(7,2,'probe_gap_seven_hsix_source_complement.json'),
        verify(8,1,'probe_gap_eight_hsix_source_complement.json')]
    sharp=[]
    for alpha in (2,3,5,10):
        g=alpha+11;A=reverse_arm(alpha,[2]*6);B=reverse_arm(1,[alpha+8]*g)
        p=[0]*(len(A)+len(B)-1)
        for i,v in enumerate(A):
            for j,w in enumerate(B):p[i+j]+=v*w
        j=alpha+11;n=len(p)-1-j
        current=2*p[n]-p[n-1];upper=2*p[n+1]-p[n]
        assert (current,upper)==(17,20),(alpha,current,upper)
        assert 2*p[2]-3*p[1]+p[0]==g*g+14*g+35
        sharp.append(dict(alpha=alpha,h=6,V_capacity=alpha+8,V_count=g,kappa=alpha+9,
            source_gap=9,j=j,tail=current,next_tail=upper,head1_budget=g*g+14*g+35))
    out=dict(status='PASS_INDEPENDENT_UNIFORM_GAP_EIGHT_HSIX_COMPLETE_COMPLEMENTS',
        configurations=configs,sharp_actual_gap_nine_profiles=sharp,seconds=time.monotonic()-start,
        scope='ALLinitialruns/capacities/ranksforgap7alpha>=2andgap8alpha>=1,ownerh>=6byPROVEDdegree/CIreductionsandEXACTalpha-clamp. Gap7alpha1kappa8andALLd<=6previouslyPROVED. Producerforward/binomialvsINDEPENDENTreverse/maxpart/individualratiosALLlayers/hashesagree. WrittenjoiningneededforUNBOUNDEDgap8theorem;sharpactualgap9tail17to20headpays. GeneraloriginalUIOPEN.')
    (ROOT/'verify_gap_eight_hsix_source_complement.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':main()
