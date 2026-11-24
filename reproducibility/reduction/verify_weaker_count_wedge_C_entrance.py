"""Independent positive-suffix and reverse-division audit of the weaker count cone."""
from pathlib import Path
import sys,json,re,hashlib
from random import Random
from itertools import accumulate
from collections import Counter
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_ordinary_golden_growth_source import infinite_ones
from verify_physical_boundary_golden_C import reference,conv
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_arbitrary_Fibonacci_tail_late_C import sign,sub,add,mul,power,evaluate
Q=(-1,1);PHI=(0,1);PSI=(1,-1);ONE=(1,0)
BOUNDARY=['reference_amplification_all_large','reference_mass_two_fifths','interval_product_sum_margin',
 'reference_previous_read_budget','finite_padding_positive_correction','uniform_actual_golden_gap',
 'renewal_response_prefix_bound','loss_cumulative_prefix_bound','geometric_interval_lower',
 'all_distance_boundary_constant','increasing_pair_source_bound','complete_C_payment','wedge_head_and_weight_geometry']
ENTRANCE=['golden_rational_two_sided','CI_prefix_mass_bound','ordinary_positive_kernel_upper',
 'padding_one_ordinary_gap_upper','finite_padding_next_correction','next_actual_golden_gap',
 'seed_budgets_padding_one','seed_budgets_padding_two','seed_budgets_padding_at_least_three',
 'preceding_ordinary_ratio_resource','ordinary_seed_transfer','complete_missing_prefix_reads',
 'weaker_wedge_geometry','nine_gap_new_wedge_or_small','reference_entry_cumulative_resource']

def kernels(stem,names):
    src=(ROOT/(stem+'.lean')).read_text();log=(ROOT/(stem+'.log')).read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==len(names)
    out={}
    for n in names:
        m=re.search(re.escape("'"+stem+'.'+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out

def at(A,j):
    return A[j] if 0<=j<len(A) else 0

def main():
    qa=json.loads((ROOT/'audit_weaker_count_wedge_C_entrance.json').read_text())
    assert qa['status']=='EXACT_QA_WEAKER_COUNT_WEDGE_ENTIRE_C_ENTRANCE_UNDER_AUDIT'
    rng=Random(20261031227);ct=Counter();sha=hashlib.sha256();profiles=[]
    for delta in range(5,36):
        for r in range(2,7):
            w=max((13*delta-27)//4,33-delta);u=w-r;h=u+delta
            if u<0 or h<2*r:continue
            for balanced in (False,True):
                ds=[2]*r
                for j in range(h-2*r):ds[j%r if balanced else -1]+=1
                profiles.append((u,sorted(d+1 for d in ds)))
    for _ in range(90):
        V=sorted(rng.choices(range(3,24),k=rng.randint(2,9)));h=sum(t-1 for t in V)
        upper=(4*(h+len(V))+30)//17
        if upper>=5 and sum(V)>=33:
            profiles.append((h-rng.randint(5,upper),V))
    for u,V in profiles:
        r=len(V);h=sum(t-1 for t in V);W=h+r;w=u+r;delta=h-u;n=delta-2
        assert W>=33 and delta>=5 and 13*delta<=4*w+30
        L=[1]
        for t in V:L=conv(L,[1]*t)
        E=L[:]
        for _ in range(u):E=conv(E,[1,1])
        head=list(accumulate(E))
        for j in range(1,n+1):
            assert 4*E[j]>=9*E[j-1];ct['independent_complete_CI_head_reads']+=1
        assert 8*E[n+1]>=15*E[n]
        I=infinite_ones([2]*u+V,W+1);R=reference(V,W+1);gr=list(accumulate(R))
        rd=[0,0]+[R[j]-R[j-1] for j in range(2,len(R))]
        x,y=rd[W:W+2];P=1;M=1
        for t in V:P*=t;M=t*M-1
        assert 5*M<=2*x and 20*rd[W-1]<=13*x
        assert 5*gr[W-4]>=3*x and 5*gr[W-3]>=6*x
        J=reverse_divided(L,u);c=mul(power(PSI,u),evaluate(L,(0,-1)))
        f=[add(J[j],mul(c,power(PSI,j))) for j in range(n+2)]
        rho=ONE
        for t in V:rho=mul(rho,mul(Q,sub(ONE,power(PSI,t))))
        assert (-I[W]+I[W-1],I[W-1]-I[W-2])==add(sub(PHI,mul(power(PHI,2),rho)),f[n])
        assert (-I[W+1]+I[W],I[W]-I[W-1])==add(mul(PHI,rho),f[n+1])
        U=[add(mul(Q,(head[j],0)),mul(power(Q,2),f[j])) for j in (n-1,n)]
        assert (-I[W],I[W-1])==sub(U[1],rho)
        assert (-I[W-1],I[W-2])==sub(add(U[0],mul(PHI,rho)),PHI)
        ct['independent_reverse_quotient_and_ordinary_kernel_identities']+=4
        # All padding classes: exact truncation I-cum(E), validated below by positive boxes.
        for alpha in range(1,delta+2):
            Fs=[I[k]-(head[k-alpha-w-1] if k-alpha-w-1>=0 else 0) for k in range(W-2,W+2)]
            fm,f0,f1,f2=Fs;a=f1-f0;b=f2-f1;gap=(-b,a)
            assert sign(sub(mul((8,0),(-a,f0-fm)),(13*E[n-1],0)))>=0
            assert sign(sub(mul((4,0),gap),(5*E[n],0)))>=0
            if b>a>0:
                assert a*f1-b*f0>0 and a*f0-b*fm>0
                ct['independent_ALL_padding_two_ordinary_seeds']+=2
            ct['independent_ALL_padding_gap_classes']+=1
        for alpha in {1,2,3,delta+1}:
            F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
            assert F[W-2:W+2]==[I[k]-(head[k-alpha-w-1] if k-alpha-w-1>=0 else 0) for k in range(W-2,W+2)]
            G=list(accumulate(F));D=[0,0]+[max(0,F[j]-F[j-1]) for j in range(2,len(F))]
            a,b=D[W:W+2]
            if b>a>0:
                for k in range(1,W+1):
                    assert a*G[k]>=b*G[k-1]
                    ct['independent_positive_box_STRONG_entrance_reads']+=1
                assert a*F[W]>b*F[W-1] and a*F[W-1]>b*F[W-2]
            # Every C shift at every later current by the exact running prefix minimum.
            best=1
            for N in range(4,len(F)):
                k=N-3
                if G[k]*G[best-1]<G[best]*G[k-1]:best=k
                if N>=W:
                    assert G[best]*D[N-1]>=G[best-1]*D[N]
                    ct['independent_positive_box_entire_halfline_C_minima']+=1
            ct['independent_positive_box_hosts']+=1
        ct['independent_profiles_outside_OLD_cone']+=4*w+17<13*delta
        sha.update(json.dumps([u,V,x,M,I[W-2:W+2]],separators=(',',':')).encode())
        ct['independent_CI_profiles']+=1
    deps=['previous_boundary_C_verification.json','physical_boundary_golden_C_verification.json',
          'ordinary_golden_growth_source_verification.json','golden_tail_large_shift_C_verification.json',
          'sharp_CI_count_wedge_verification.json','two_factor_complete_entrance_verification.json',
          'multitail_binary_prefix_finite_principle_verification.json','general_one_jump_analytic_C_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():
            assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['weaker_count_wedge_C_entrance_proof.tex','CountWedgeBoundaryPositive.lean','CountWedgeBoundaryPositive.log',
           'WeakerCountWedgeC.lean','WeakerCountWedgeC.log','audit_weaker_count_wedge_C_entrance.py',
           'audit_weaker_count_wedge_C_entrance.json','verify_weaker_count_wedge_C_entrance.py']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNBOUNDED_WEAKER_COUNT_WEDGE_ALL_PADDING_C_FROM_PHYSICAL_W',new_scoped_reports=28,
      kernels={'CountWedgeBoundaryPositive':kernels('CountWedgeBoundaryPositive',BOUNDARY),'WeakerCountWedgeC':kernels('WeakerCountWedgeC',ENTRANCE)},
      state_sha256=qa['state_sha256'],QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),
      new_finite_entrance_certificates=0,
      theorem='PROVED ALL actual normalized1^alpha2^uV,allpadding/counts/capacities/ranks/shiftsUNBOUNDED: if4w+30>=13delta (equiv17u+4r+30>=13h), EVERYCshift>=3 atEVERYcurrentN>=W. r1/lowdelta/weight<=32 use OLDcomplete results. Remainingunboundedcase hasW>=33,delta>=5,r>=2. ALLfiniteQAonly; no new finite entrance premise.',
      boundary_resource='PROVED correct finite-padding D golden correction Ecurrent-phiEprevious isNONNEGATIVE throughtwo needed reads. ExactphysicalW gap>=13/8 E_(delta-3). Reference mass<=2/5 currentD,previousD<=13/20currentD,twocumulative resources>=3/5 and6/5currentD. ALLdistance243/32E resource exceedsFULL198/29E loss,margin711/928E.',
      entrance='PROVED ALLpadding TWO actual ordinaryseeds atW-1/W whenD_(W+1)>D_W>0; exact ordinarypositivekernel includes missingtopunitphi. Separatealpha1/alpha2/alpha>=3 budgets closeALLstrongGprefixreads throughW. UniversalpremodeDLC propagatesEVERYlatercurrent usingitsOWNratio. Flatentry handledbyDLC,notUIalone; no generic ordinaryLC claimed.',
      uniform_nine_gap='PROVED ALLu>=h-9,EVERYactualCshift>=3 atEVERYcurrentN>=W. Newcone failure withdelta<=9 forcesW<=30,OLDweight32completeC paysALL. No new finite table.',
      uniform_five_gap='PROVED ALLu>=h-5,EVERYactualCshift>=3 atEVERYcurrentN>=W-1: registeredW-1boundaryplusnewhalflineW closesOLDu=h-5/currentW gap.',
      formal_scope='TWENTY-EIGHT NEW standard-axiom scoped Lean reports; full arbitrary-prefix renewal/CI/cumulative/geometric and finite-product inductions,allpaddingbudgetalgebra/allintegerconeguards. Model/root/CI identification and full sequence assembly WRITTEN,not end-to-end actual-arm Lean. Earlierfourfinite referenceprefixcertificates reused,notrecounted.',
      remaining='GeneralC atN<W-1 and complementary countcone,fullA2 andoriginalunamplified coefficientUIremainOPEN. LateC residual nowdelta>=10,newconeviolation17u+4r+30<13h,W>32 andpreviousautomaticconeviolations. FirstunresolvedfullCnononecount6unchanged. No CDFLC/finiteQA substitution fororiginalUI.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'weaker_count_wedge_C_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)

if __name__=='__main__':main()

