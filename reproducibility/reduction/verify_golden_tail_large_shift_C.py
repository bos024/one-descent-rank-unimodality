"""Independent positive-box and full read-domain verification of the universal large-shift resource."""
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
from probe_divided_CI_positive_primitive import divided
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,mul,power

NAMES=['monotone_divided_head','crossing_entry_parity','midpoint_entry_geometry','helpful_signed_spectral_entry',
       'geometric_inverse_entry','finite_density_golden_transfer','LC_growth_ceiling_step','golden_large_shift_C_paid','source_band_read_domain']

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def kernels():
    src=(ROOT/'GoldenTailLargeShiftC.lean').read_text(encoding='utf8');log=(ROOT/'GoldenTailLargeShiftC.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(NAMES)
    out={}
    for name in NAMES:
        hit=re.search(r"'GoldenTailLargeShiftC\."+name+r"' depends on axioms: \[([^]]*)\]",log);assert hit,name
        ax={x.strip() for x in hit.group(1).split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};out[name]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_golden_tail_large_shift_C.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_UNIVERSAL_GOLDEN_TAIL_AND_LARGE_SHIFT_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();contexts=[]
    for u in range(1,26):
        for h in {u+1,u+2,3*u-2,3*u+2}:
            if h<=u:continue
            for r in range(1,min(5,h//2)+1):
                ds=[2]*r;extra=h-2*r
                for k in range(extra):ds[k%r]+=1
                contexts.append((u,[d+1 for d in sorted(ds)]))
    rng=Random(20261031151)
    for _ in range(80):
        V=sorted(rng.choices(range(3,20),k=rng.randint(1,9)));h=sum(t-1 for t in V);contexts.append((rng.randint(1,h-1),V))
    for u,V in contexts:
        r=len(V);h=sum(t-1 for t in V);delta=h-u;W=h+r;w=u+r
        L=[1]
        for t in reversed(V):L=conv([1]*t,L)
        E,J=divided(L,u);Inf=suffix_boxes(delta+1,[2]*u+V);inf0=Inf[W]-Inf[W-1];inf1=Inf[W+1]-Inf[W]
        assert J[delta-1]==(-inf1,inf0)
        if h<=3*u+2:assert sign(J[delta-1])>0;ct['independent_positive_quotient_entries']+=1
        else:assert inf1<=inf0
        for alpha in {1,2,delta+1}:
            F=suffix_boxes(alpha,[2]*u+V);G=list(accumulate(F));D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
            if D[W]>0:assert D[W+1]*inf0<=D[W]*inf1
            best=1;mins=[0]*(w+2)
            for k in range(1,w+2):
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                mins[k]=best
            for N in range(W+1,len(F)):
                if D[N-1]:assert sign((-D[N],D[N-1]))>0;ct['independent_entire_positive_tail_golden_bounds']+=1
                else:assert D[N]==0
                kmax=min(w+1,N-3)
                if kmax>=1:
                    k=mins[kmax];assert G[k]*D[N-1]>=G[k-1]*D[N];ct['independent_all_large_shift_C_minimum_products']+=1
            ct['independent_actual_hosts']+=1
        ct['independent_CI_profiles']+=1;sha.update(json.dumps([u,V,J[delta-1],inf0,inf1]).encode())
    # Reconstruct the complete actual source/S witness by a different ordinary enumerator.
    A=suffix_boxes(21,[2]*20+[3]*20)[:122];B=suffix_boxes(50,[19]*18)[:393];j=60;N=61;t=452;n=453;k=1
    GA=list(accumulate(A));DA=[0,0]+[max(0,A[i]-A[i-1]) for i in range(2,len(A))]
    AB=conv(A,B);EB=[0,0]+[2*B[i-1]-B[i] for i in range(2,len(B))];H=conv(EB,A)
    assert next(i for i,z in enumerate(EB) if z)==20 and all(EB[i]>=EB[i-1] for i in range(1,N+1))
    assert A[N]>A[N-1] and B[N]>B[N-1]
    weighted_sum=0
    for shift in range(20,N+1):
        assert N-shift<=41
        prev=GA[N-shift-1] if N-shift>=1 else 0
        margin=GA[N-shift]*DA[j]-prev*DA[N];assert margin>=0
        weight=EB[shift]-EB[shift-1];assert weight>=0;weighted_sum+=weight*margin
        ct['independent_literal_source_C_read_guards']+=1
    assert weighted_sum==H[N]*DA[j]-H[j]*DA[N]>=0
    cur=2*AB[j]-AB[N];prev=2*AB[j-1]-AB[j];assert cur>=0 and cur-prev>=0
    p=conv(A[::-1],B[::-1]);pos=[max(0,p[i]-(p[i-1] if i else 0)) for i in range(len(p))];wt=[v*2**i for i,v in enumerate(pos)];ell=wt.index(max(wt))
    assert ell==227 and p.index(max(p))==228 and all(wt[i]<=wt[i+1] for i in range(ell)) and all(wt[i]>=wt[i+1] for i in range(ell,len(wt)-1))
    vn=p[n-1]-p[n];vn1=p[n]-p[n+1];Smargin=2*(pos[k+1]+vn1)-pos[k]-vn
    witness=qa['local_S_witness']
    assert k<ell and k<121 and n<121+t and p[n]-p[k]>0
    assert [cur,cur-prev,weighted_sum,Smargin,p[n]-p[k]]==[witness['nonnegative_current_source'],witness['source_nonrecovery_margin'],witness['source_ratio_margin'],witness['S_margin'],witness['new_raw_window_positive_difference']]
    deps=['two_factor_complete_entrance_verification.json','four_subdegree_C_entrance_verification.json',
          'automatic_late_C_cones_verification.json','homogeneous_reference_and_sharp_entrance_verification.json']
    for path in deps:
        dep=json.loads((SOURCE/path).read_text(encoding='utf8'))
        for name,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==digest,name
    names=['universal_golden_tail_large_shift_C_proof.tex','GoldenTailLargeShiftC.lean','GoldenTailLargeShiftC.log',
           'audit_golden_tail_large_shift_C.py','audit_golden_tail_large_shift_C.json','verify_golden_tail_large_shift_C.py',
           'finite_initial_ones_relative_derivative.tex','C_to_coupled_S_rising_window.tex','CToCoupledSRisingWindow.lean','CToCoupledSRisingWindow.log']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNIVERSAL_GOLDEN_TAIL_LARGE_SHIFT_C_AND_LOCAL_S_RESOURCE',new_scoped_reports=9,kernels={'GoldenTailLargeShiftC':kernels()},
        state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
        golden_tail='PROVED ALLh>u,ALLcapacities/counts/paddings: actual positive D_N<phi*Dprev at EVERYN>=W+1 with Dprev>0; if Dprev0 then D_N0. Helpful spectral parity at natural quotient entry makes c*(-q)^(delta-1)<0. Finite monotone CI head gives positive entry below symmetric middle; old automatic cone covers complement; finite-padding density and universal tail-D-LC propagate. No finite premise.',
        large_shift_C='PROVED ALL actual1^alpha2^uV with nonemptyV>=3,ALLh/u,ALLpadding: everyC comparison at N>=W+1,R>=max(3,N-u-r-1) holds. Forh>u use protected actual G prefix throughu+r+1 and universal golden D ceiling. Forh<=u old complete late C already gives every shift. This covers arbitrary CI profiles OUTSIDE all registered whole-arm wedges.',
        local_source_S='PROVED local BOTH-ordinary-rising source nonrecovery without FULL ownerC whenever owner currentj>=W_A and j<=u_A+r_A+kappa_B, with usual nonnegative CURRENT reverse source and actual positive D/source-monotonicity guards. All opposite source shifts are in the proved LARGE-SHIFT C read domain. Coupled S additionally retains OLD weighted-A2 head and physical guards. No full induction, no original UI theorem, no claim of novelty for the reused C-to-S algebra.',
        actual_witness=witness,
        formal_scope='NINE scoped kernel reports include an ALL-prefix monotone division induction,exact natural crossing parity,inverse/density/growth and C comparisons,and complete source read-domain guard. Actual model/CI symmetry/source identities/mode and weighted-source assemblies WRITTEN, not an end-to-end Lean composition/A2 proof. Reused C-to-S reports NOT recounted; ALL finite checks and the guarded example QA ONLY.',
        remaining='All-shift late C outside whole-arm union remains OPEN for the SHORTER shifts R<N-u-r-1. Earlier actual/reference C, complete general A2 and original unamplified coefficient UI remain OPEN. Universal golden growth and local S do NOT by themselves close the original induction; first unresolved full-C count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_whole_late_C_union='u>=h-4 OR17u+4r+17>=13h UNCHANGED',
        sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in names})
    (ROOT/'golden_tail_large_shift_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','actual_witness')}),flush=True)

if __name__=='__main__':main()
