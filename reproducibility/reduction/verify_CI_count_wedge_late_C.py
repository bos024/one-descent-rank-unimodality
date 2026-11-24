"""Independent actual positive-box reconstruction of the full unbounded C wedge."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from random import Random
from collections import Counter
from itertools import accumulate
import hashlib,json,re
from verify_subdegree_CI_entrance import suffix_boxes

NAMES=['source_wedge_gives_growth','growth_sum_step','finite_loss_prefix_sum','dyadic_ternary_all_distances',
       'reference_CDF_growth_step','strict_entry_gap','double_cumulative_source_bound',
       'dyadic_reference_resource','dyadic_source_payment','prefix_read_paid','last_prefix_read_paid']

def kernels():
    src=(ROOT/'CICountWedgeLateC.lean').read_text(encoding='utf8');log=(ROOT/'CICountWedgeLateC.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(NAMES)
    out={}
    for name in NAMES:
        hit=re.search("'CICountWedgeLateC\."+name+r"' depends on axioms: \[([^]]*)\]",log);assert hit,name
        ax={x.strip() for x in hit.group(1).split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[name]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_CI_count_wedge_late_C.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_UNBOUNDED_CI_COUNT_WEDGE_LATE_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();contexts=[]
    for delta in range(5,17):
        for r in range(1,7):
            u=4*delta-5-r;h=u+delta
            if h<2*r:continue
            extra=h-2*r
            for balanced in (False,True):
                ds=[2]*r
                if balanced:
                    for k in range(extra):ds[k%r]+=1
                else:ds[-1]+=extra
                contexts.append((u,[d+1 for d in sorted(ds)]))
    rng=Random(20261031111)
    for _ in range(100):
        V=sorted(rng.choices(range(3,20),k=rng.randint(1,10)));h=sum(t-1 for t in V);dmax=(h+len(V)+5)//5
        if dmax>=5:
            delta=rng.randint(5,dmax);contexts.append((h-delta,V))
    for u,V in contexts:
        h=sum(t-1 for t in V);delta=h-u;r=len(V);w=u+r;W=h+r;p=delta-2;N0=w+2
        assert w>=4*delta-5
        R=suffix_boxes(h+2,[2]*(h+1)+V);g=list(accumulate(R));x=R[W]-R[W-1];y=R[W+1]-R[W];A=x*x+x*y-y*y
        assert x>=2 and 2*y>=3*x and A>0 and R[W-2]==x-1 and R[W-1]==y
        for n in range(1,W+2):assert g[n]<=2*g[n-1];ct['independent_reference_dyadic_CDF_comparisons']+=1
        for alpha in {1,2,delta,delta+1,u+h+2}:
            F=suffix_boxes(alpha,[2]*u+V);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            l=[(R[N0+j]-R[N0+j-1])-raw[N0+j] for j in range(p+2)]
            for j in range(1,p+2):assert j*l[j]>=(w-j+1)*l[j-1] and l[j]>=3*l[j-1];ct['independent_literal_loss_triple_growth_comparisons']+=1
            a=sum(l[:p]);b,c=l[p:p+2];assert 2*a<=b and c>=3*b
            if D[W+1]>D[W]>0:
                d0,d1=D[W],D[W+1];assert F[W]*d0-F[W-1]*d1>0
                for k in range(1,W+1):assert G[k]*d0>=G[k-1]*d1;ct['independent_all_prefix_C_seed_products']+=1
                for j in range(p+1):
                    k=N0+j;d=p-j
                    resource=g[k]*d0-g[k-1]*d1;source=(g[k]-G[k])*d0-(g[k-1]-G[k-1])*d1
                    if d:
                        assert resource*2**d>b*d0 and 2*3**d*source<=3*b*d0
                    else:assert 2*resource>3*b*d0 and 2*source<=3*b*d0
                    ct['independent_literal_dyadic_ternary_prefix_payments']+=1
                ct['independent_strictly_growing_boundary_hosts']+=1
            best=1
            for N in range(4,len(F)):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N<W+1:continue
                assert G[best]*D[N-1]>=G[best-1]*D[N];ct['independent_all_shift_C_minimum_payments']+=1
                if r<=2 and delta<=8:
                    for k in range(1,N-2):assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_literal_C_read_products']+=1
            sha.update(json.dumps([u,V,alpha,l,F],separators=(',',':')).encode());ct['independent_actual_hosts']+=1
        ct['independent_CI_profiles']+=1
    deps=['four_subdegree_C_entrance_verification.json','two_factor_complete_entrance_verification.json',
          'homogeneous_reference_and_sharp_entrance_verification.json']
    for path in deps:
        dep=json.loads((SOURCE/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==digest,name
    names=['CI_count_wedge_late_C_proof.tex','CICountWedgeLateC.lean','CICountWedgeLateC.log',
           'audit_CI_count_wedge_late_C.py','audit_CI_count_wedge_late_C.json','verify_CI_count_wedge_late_C.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNBOUNDED_ACTUAL_CI_COUNT_WEDGE_LATE_C',new_scoped_reports=11,kernels={'CICountWedgeLateC':kernels()},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        wedge='PROVED ALL actual sorted1^alpha2^uV,ALLcapacities/counts/paddings,EVERYCshift>=3 at EVERYN>=W+1 IF w=u+r>=4(h-u)-5, equivalently5u+r+5>=4h. delta<=4 uses old all-padding theorem; ENTIRE delta>=5 cone is a NEW UNBOUNDED analytic argument. No finite entrance premise.',
        cumulative_payment='ENTIRE ordinary-source cumulative and double-cumulative losses retained: lj triple growth throughp+1 pays EVERY initial G prefix directly. Reference G has ratios>phi and dyadic UPPER bound; at distance d>=1, 3*2^d<=2*3^d compares source and background. Last read uses y>=3x/2. This does NOT assume reference or actual cumulative LC, nor any earlier reference C.',
        ordinary_seed='ONE actual ordinary seed at W follows from total earlier loss a<=b/2, next loss c>=3b, x>b and positive reference Cassini amplitude. Previously registered UNIVERSAL late-D-LC integrates all later F/G reads. Both loss sources and leading numerator unit retained.',
        formal_scope='ELEVEN scoped kernel reports include a genuine FINITE-SUM induction for loss prefixes and an ALL-natural-distance dyadic/ternary induction, plus complete real entry/prefix payments. CI source/model/reference/mode identities and read integration are WRITTEN assemblies of already registered inputs, not an end-to-end Lean composition theorem. Every finite profile here is QA ONLY.',
        remaining='Potential actual LATE-C failures now ALSO require5u+r+5<4h, in addition to oldu>=9,u+5<=h<=3u-2,maxcap<=2u-1,W>32. Earlier actual/reference C, general C/A2/original coefficient UI remain OPEN. First original unresolved full-C nonone count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_union='u>=h-4 OR 5u+r+5>=4h',
        sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in names})
    (ROOT/'CI_count_wedge_late_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
