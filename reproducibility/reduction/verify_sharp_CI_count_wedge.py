"""Independent actual positive-box reconstruction of the full unbounded C wedge."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from random import Random
from math import prod
from collections import Counter
from itertools import accumulate
import hashlib,json,re
from verify_subdegree_CI_entrance import suffix_boxes

NAMES=['interval_amplification_all_capacities','fifteen_rank_amplification','reference_mass_budget','reference_ratio_eight_fifths','reference_cumulative_mass_resources','sharp_wedge_geometry','sharp_wedge_source_growth','doubling_loss_finite_sum','sharp_entry_gap','sharp_interior_prefix_paid','sharp_last_prefix_paid','sharp_ordinary_seed']

def kernels():
    src=(ROOT/'SharpCICountWedge.lean').read_text(encoding='utf8');log=(ROOT/'SharpCICountWedge.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(NAMES)
    out={}
    for name in NAMES:
        hit=re.search(r"'SharpCICountWedge\."+name+r"' depends on axioms: \[([^]]*)\]",log);assert hit,name
        ax={x.strip() for x in hit.group(1).split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[name]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_sharp_CI_count_wedge.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_SHARP_ACTUAL_CI_COUNT_WEDGE_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();contexts=[]
    for delta in range(5,17):
        for r in range(1,7):
            w=(13*delta-17+3)//4;u=w-r;h=u+delta
            if h<2*r:continue
            extra=h-2*r
            for balanced in (False,True):
                ds=[2]*r
                if balanced:
                    for k in range(extra):ds[k%r]+=1
                else:ds[-1]+=extra
                contexts.append((u,[d+1 for d in sorted(ds)]))
    rng=Random(20261031131)
    for _ in range(100):
        V=sorted(rng.choices(range(3,20),k=rng.randint(1,10)));h=sum(t-1 for t in V);dmax=(4*(h+len(V))+17)//17
        if dmax>=5:
            delta=rng.randint(5,dmax);contexts.append((h-delta,V))
    for u,V in contexts:
        h=sum(t-1 for t in V);delta=h-u;r=len(V);w=u+r;W=h+r;p=delta-2;N0=w+2
        assert 4*w+17>=13*delta
        R=suffix_boxes(h+2,[2]*(h+1)+V);g=list(accumulate(R));x=R[W]-R[W-1];y=R[W+1]-R[W];A=x*x+x*y-y*y
        assert x>=2 and 5*y>=8*x and A>0 and R[W-2]==x-1 and R[W-1]==y
        B=[R[n]-(R[n-1] if n else 0)-(R[n-2] if n>1 else 0) for n in range(W+1)]
        assert all(z>=0 for z in B);M=sum(B)
        assert 0<M<prod(V) and 2*M<=x
        assert g[W-2]==x+y-M and g[W-1]==x+2*y-M and g[W-2]>=2*x and 2*g[W-1]>=7*x
        ct['independent_numerator_mass_resources']+=1
        for n in range(1,W+2):assert g[n]<=2*g[n-1];ct['independent_reference_dyadic_CDF_comparisons']+=1
        for alpha in {1,2,delta,delta+1,u+h+2}:
            F=suffix_boxes(alpha,[2]*u+V);G=list(accumulate(F));raw=[1]+[F[n]-F[n-1] for n in range(1,len(F))];D=[max(0,z) for z in raw]
            l=[(R[N0+j]-R[N0+j-1])-raw[N0+j] for j in range(p+2)]
            for j in range(1,p+2):assert j*l[j]>=(w-j+1)*l[j-1] and 4*l[j]>=9*l[j-1];ct['independent_literal_loss_nine_quarters_growth_comparisons']+=1
            a=sum(l[:p]);b,c=l[p:p+2];assert a<=b and 4*c>=9*b
            if D[W+1]>D[W]>0:
                d0,d1=D[W],D[W+1];assert 20*(F[W]*d0-F[W-1]*d1)>=20*A+7*b*b
                for k in range(1,W+1):assert G[k]*d0>=G[k-1]*d1;ct['independent_all_prefix_C_seed_products']+=1
                for j in range(p+1):
                    k=N0+j;d=p-j
                    resource=g[k]*d0-g[k-1]*d1;source=(g[k]-G[k])*d0-(g[k-1]-G[k-1])*d1
                    if d:
                        assert 8*resource*2**d>20*b*d0 and source*2**d<=2*b*d0
                    else:assert 16*resource>35*b*d0 and source<=2*b*d0
                    ct['independent_literal_sharp_dyadic_prefix_payments']+=1
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
        ct['independent_CI_profiles']+=1;ct['independent_profiles_beyond_previous_wedge']+=w<4*delta-5
    deps=['CI_count_wedge_late_C_verification.json','four_subdegree_C_entrance_verification.json','two_factor_complete_entrance_verification.json',
          'homogeneous_reference_and_sharp_entrance_verification.json']
    for path in deps:
        dep=json.loads((SOURCE/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==digest,name
    names=['sharp_CI_count_wedge_late_C_proof.tex','SharpCICountWedge.lean','SharpCICountWedge.log',
           'audit_sharp_CI_count_wedge.py','audit_sharp_CI_count_wedge.json','verify_sharp_CI_count_wedge.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNBOUNDED_SHARPER_ACTUAL_CI_COUNT_WEDGE_LATE_C',new_scoped_reports=12,kernels={'SharpCICountWedge':kernels()},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        reference_mass='PROVED ALL reference CI words with W>=15: entire nonnegative numerator mass M=B(1)=prodV-Aproper<=Dref(W)/2. NEW all-capacity induction phi^t*S_t(q)>=t*(8/7)^t is kernel checked for EVERYt>=3; product and Binet assemblies give x>=2prodV. This is NOT a finite-capacity extrapolation.',
        reference_resources='PROVED W+r>=12 gives y>=8x/5 by old whole-word norm and t<=q10=34-55q. Exact coefficient identity Gref(n)=Fref(n+2)-prefixB(n+2) yields Gref(W-2)>=2x and Gref(W-1)>=7x/2. No cumulative LC assumed.',
        source_and_seed='CI-count cone4w+17>=13delta makes every required loss ratio>=9/4; doubling finite-sum induction gives entire source prefix<=2current loss. Stronger reference mass pays EVERY G read, including the last. With earlier total loss a<=b, generic ordinary determinant has NEW margin Q>=A+7b2/20>0; universal late-D-LC integrates all later C reads.',
        wedge='PROVED EVERY sorted actual1^alpha2^uV with nonemptyV>=3: 17u+4r+17>=13h implies EVERYCshift>=3 at EVERYN>=W+1,ALLcapacities/counts/paddings. delta<=4 old; ENTIRE delta>=5 new cone is analytic and unbounded, W>=17. NO NEW FINITE ENTRANCE PREMISE.',
        formal_scope='TWELVE new scoped kernel reports include ALL-NATURAL-CAPACITY interval amplification and a genuine finite-sum loss induction, whole reference-mass/ratio and complete source/ordinary/prefix payments. Product, Binet, coefficient/source, actual mode and read-integration assembly WRITTEN, not end-to-end Lean composition theorem. All finite profiles QA ONLY.',
        remaining='Actual late C now holds in UNIONu>=h-4 OR17u+4r+17>=13h. Potential failures requireu>=9,u+5<=h<=3u-2,maxcap<=2u-1,W>32,AND17u+4r+17<13h. Earlier actual/reference C, general C/A2/original coefficient UI remain OPEN; first original unresolved full-C count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_union='u>=h-4 OR17u+4r+17>=13h',
        sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in names})
    (ROOT/'sharp_CI_count_wedge_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
