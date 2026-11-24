"""Independent positive-box reference and actual h=u+3 late-C reconstruction."""
from pathlib import Path
from itertools import accumulate
from random import Random
from collections import Counter
import json,hashlib,sys
from verify_double_subdegree_CI_entrance import multiplicities
from verify_subdegree_CI_entrance import suffix_boxes
from verify_divided_CI_surplus_three_primitive import kernel
ROOT=Path(__file__).resolve().parent
NAMES=['all_padding_three_loss_payments','first_ordinary_seed_identity','second_ordinary_seed_identity',
       'first_ordinary_seed_paid','second_ordinary_seed_paid','strict_subgolden_actual_entrance']

def main():
    qa=json.loads((ROOT/'audit_triple_subdegree_C_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_TRIPLE_SUBDEGREE_ACTUAL_LATE_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();contexts=[]
    for h in range(4,15):
        for V in multiplicities(h,h):contexts.append((h-3,V))
    rng=Random(202610291221)
    for _ in range(115):
        V=sorted(rng.choices(range(3,22),k=rng.randint(1,9)));u=sum(t-1 for t in V)-3
        if u>=0:contexts.append((u,V))
    for u,V in contexts:
        h=u+3;r=len(V);W=h+r;w=u+r
        # A genuinely actual, positive-box model of the reference prefix:
        # U=h+1 starts its first binary defect at W+3, beyond every reference read.
        R=suffix_boxes(h+2,[2]*(h+1)+V);x=R[W]-R[W-1];y=R[W+1]-R[W];A=x*x+x*y-y*y
        assert [R[W-2],R[W-1],R[W]]==[x-1,y,x+y] and A>0
        for alpha in {1,2,3,4,5,u+h+3}:
            F=suffix_boxes(alpha,[2]*u+V);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            a=(R[W-1]-R[W-2])-raw[W-1];b=x-raw[W];c=y-raw[W+1]
            E2=(w*w-w)//2+r
            expected=(2,2*w+1,2*E2+w+2) if alpha==1 else (1,w+2,E2+2*w+2) if alpha==2 else (1,w+1,E2+w+3) if alpha==3 else (1,w+1,E2+w+2)
            assert (a,b,c)==expected
            P=F[W-1]*D[W]-F[W-2]*D[W+1]
            Q=F[W]*D[W]-F[W-1]*D[W+1]
            if w>=6:
                assert c>=3*b and b>=2*a
                # Use raw signed slopes for the identity, whether or not D survives.
                assert F[W-1]*raw[W]-F[W-2]*raw[W+1]>=2
                assert F[W]*raw[W]-F[W-1]*raw[W+1]>0
            if D[W+1]>D[W]>0:
                assert P>=2 and Q>0
                for k in range(1,W+1):assert G[k]*D[W]>=G[k-1]*D[W+1];ct['independent_all_prefix_boundary_seeds']+=1
            best=1
            for N in range(4,len(F)):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N<W+1:continue
                assert G[best]*D[N-1]>=G[best-1]*D[N];ct['independent_all_shift_minimum_C_payments']+=1
                if u<=18 and r<=3:
                    for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_literal_C_read_products']+=1
            ct['independent_actual_hosts']+=1;sha.update(json.dumps([u,V,alpha,F],separators=(',',':')).encode())
        ct['independent_CI_profiles']+=1
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_TRIPLE_SUBDEGREE_ACTUAL_LATE_C',counts=dict(ct),state_sha256=sha.hexdigest())),flush=True);return
    kernels={'TripleSubdegreeCEntrance':kernel('TripleSubdegreeCEntrance',NAMES)}
    deps=['two_factor_complete_entrance_verification.json','double_subdegree_CI_entrance_verification.json',
          'automatic_late_C_cones_verification.json','homogeneous_reference_and_sharp_entrance_verification.json']
    for path in deps:
        dep=json.loads((ROOT/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    files=['triple_subdegree_C_entrance_proof.tex','TripleSubdegreeCEntrance.lean','TripleSubdegreeCEntrance.log',
           'audit_triple_subdegree_C_entrance.py','audit_triple_subdegree_C_entrance.json',
           'verify_triple_subdegree_C_entrance.py','homogeneous_reference_complete_C.tex']+deps
    out=dict(status='PASS_UNBOUNDED_TRIPLE_SUBDEGREE_ALL_PADDING_ACTUAL_LATE_C',new_scoped_reports=6,kernels=kernels,
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        losses='EXACT h=u+3 first finite-binary reference loss at W-1, derivative z^(W-1)E/(1-z-z2), PLUS distinct initial-ones loss z^(W+alpha-2)E. E0=1,E1=w,E2=choose(w,2)+r. ALL four alpha regimes retained throughW+1; losses satisfy 1<=a<=2,b>=2a,c>=3b atw>=6.',
        entrance='PROVED ANY realx>=2,x<=y<=2x,A=x2+xy-y2>0,1<=a<=2,b>=2a,c>=3b: exact TWO ordinary seeds P>=2,Q>0. Reference F(W-2)=x-1 retains leading numerator unit, F(W-1)=y,F(W)=x+y. Actual tail ratio(y-c)/(x-b)<phi whenever positive. Unchanged reference G throughW-2 has ratios>phi; TWO seed integrations extend toW. UNIVERSAL late-D-LC then pays every later all-shift C read.',
        actual='PROVED ALL sorted1^alpha2^uV, h=u+3,ALLcapacities/counts/paddings, everyCshift>=3 at EVERYcurrentN>=W+1. Smallw<6 uses OLD allu<=8 theorem; no new finite entrance or exception certificate.',
        threshold='ALL actual late C now holds at u>=h-3. Oldu>=h-2 plus NEW h=u+3. Every nonbinary tail capacity/count, binary count, padding and shift is unbounded.',
        remaining='Potential actual LATE-C failures now requireu>=9,u+4<=h<=3u-2,maxcap<=2u-1,W>32. Earlier actual/reference C N<=W, general C/A2 and original coefficient UI remain OPEN. First unresolved original full-C nonone count6 unchanged.',
        formal_scope='SIX new scoped real-algebra kernel reports:complete loss-growth cone, TWO exact ordinary seed identities,TWO full unbounded seed payments and strict subgolden gap. Reference/source/model identities, mode split, prefix and TWO integrations are WRITTEN using already registered universal D-LC/reference/source inputs, not an end-to-end composition Lean theorem. All finite diagnostics QA ONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-3',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'triple_subdegree_C_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
