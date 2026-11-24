"""Independent positive-suffix verification of hereditary strong late C and crossing reduction."""
from pathlib import Path
import sys,json,re,hashlib
from itertools import accumulate,product
from collections import Counter
from random import Random
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign
NAMES=['golden_margin_constants','binary_cumulative_gap_box','all_length_tail_window_margin','head_window_atom_margin',
 'finite_window_residual_sum','adjacent_ratio_antitone','positive_LC_adjacent_ratio','subtracted_window_ratio',
 'all_prefix_ratio_lower','full_mode_ratio_cap','weighted_window_ratio_cap','rising_window_forces_rising_seed',
 'cumulative_margin_prefix_extension','smaller_ratio_preserves_margin','first_crossing_prefix',
 'prefix_sum_length_bound','bounded_crossing_has_two_factors','crossing_prefix_in_new_cone',
 'unresolved_crossing_at_most_six_suffix_factors','single_crossing_at_most_one_suffix_factor',
 'one_gap_ordinary_seed','two_gap_ordinary_seed','two_gap_all_padding_losses','low_gap_golden_ceiling']

def kernels():
    src=(ROOT/'HereditaryStrongLateC.lean').read_text();log=(ROOT/'HereditaryStrongLateC.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==24
    out={}
    for n in NAMES:
        m=re.search(re.escape("'HereditaryStrongLateC."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out

def box(alpha,u,V,ct):
    W=sum(V);F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+W+1]+[0]
    G=list(accumulate(F));D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
    a,b=D[W:W+2]
    if b>a>0:
        assert sign((-b,a))>0
        for k in range(1,W+1):
            assert sign((a*G[k]-b*G[k-1]-2*a,a))>=0
            ct['independent_positive_box_strong_additive_margins']+=1
        for n in range(W,len(F)-1):
            assert F[n]**2>=F[n-1]*F[n+1]
            ct['independent_positive_box_entire_ordinary_LC_tail']+=1
    best=1
    for N in range(4,len(F)):
        k=N-3
        if G[k]*G[best-1]<G[best]*G[k-1]:best=k
        if N>=W+1:
            assert a>=0 and G[best]*D[N-1]>=G[best-1]*D[N]
            ct['independent_positive_box_late_C_minima']+=1
    ct['independent_positive_box_hosts']+=1
    return F,G,D

def main():
    qa=json.loads((ROOT/'audit_hereditary_strong_late_C.json').read_text())
    assert qa['status']=='EXACT_QA_HEREDITARY_STRONG_LATE_C_UNDER_AUDIT'
    ct=Counter();rng=Random(20261031327);sha=hashlib.sha256()
    # Independent reference reconstruction, including every order of these small tails.
    for r in range(1,4):
        for V in product(range(3,8),repeat=r):
            gr=list(accumulate(reference(V,sum(V)+4)))
            for k in range(1,len(gr)):
                assert sign((gr[k]-2,1-gr[k-1]))>=0
                ct['independent_arbitrary_order_reference_additive_margins']+=1
    profiles=[]
    for u in (33,42,55,73,101):
        for delta in (1,2,3,4,5,7):
            h=u+delta
            for r in (2,3,7):
                ds=[2]*r
                for j in range(h-2*r):ds[j%r]+=1
                V=sorted(d+1 for d in ds)
                if 17*u+4*r+30>=13*h:profiles.append((u,V))
        for cap in (3,5,8):
            V=[];h=0
            while h<=u:V.append(cap);h+=cap-1
            profiles.append((u,V))
    for _ in range(55):
        u=rng.randint(33,115);V=[];h=0;cap=rng.randint(3,5)
        while h<=u:
            cap+=rng.randrange(2);V.append(cap);h+=cap-1
        if 4*(u+len(V))+30>=13*(h-u):profiles.append((u,V))
    for u,V0 in profiles:
        h=sum(t-1 for t in V0);delta=h-u;W=sum(V0)
        assert h>u and ((delta<=4 and u>=33) or (len(V0)>=2 and delta>=5 and W>=33 and 4*(u+len(V0))+30>=13*delta))
        for alpha in {1,2,4,delta+2}:
            V=V0[:];old=box(alpha,u,V,ct)
            for j in range(2):
                t=rng.randint(V[-1],max(V[-1],min(2*u-1,3*V[-1]+u//3)))
                new=box(alpha,u,V+[t],ct)
                F,G,D=old;NF,NG,ND=new
                W=sum(V);Wp=W+t;a,b=ND[Wp:Wp+2];x,y=D[W:W+2]
                assert a==max(0,F[Wp-1]-F[W-1]) and b==max(0,F[Wp]-F[W])
                if b>a>0:
                    assert y>x>0 and b*x<=a*y and b*F[Wp-1]<=a*F[Wp]
                    for k in range(1,Wp):
                        assert sign((a*G[k]-b*G[k-1]-2*a,a))>=0
                        ct['independent_old_G_margins_at_new_entry_ratio']+=1
                    # Full ordinary/cumulative affine model identification at every new prefix.
                    for k in range(Wp+1):
                        assert NG[k]==1+sum(G[k-i] if k>=i else 0 for i in range(1,t+1))
                        ct['independent_actual_affine_cumulative_identities']+=1
                    hh=sum(c-1 for c in V+[t]);rr=len(V)+1
                    ct['independent_strict_transfers_outside_old_countcone']+=13*hh>17*u+4*rr+30
                    ct['independent_strict_window_transfers']+=1
                V=V+[t];old=new
            sha.update(json.dumps([alpha,u,V0,V,ND[sum(V):sum(V)+2]],separators=(',',':')).encode())
    # The witness of genuinely enlarged scope is reconstructed independently.
    wit=qa['actual_new_coverage_witness'];V=wit['full_V'];u=wit['u'];alpha=wit['alpha']
    F,G,D=box(alpha,u,V,ct);W=sum(V)
    assert D[W:W+2]==wit['new_pair'] and D[W+1]>D[W]>0
    assert 13*wit['h']>17*u+4*len(V)+30 and wit['h']<=3*u-2 and max(V)<=2*u-1
    # Integer conditions are QA of universal Lean arithmetic, not finite premises.
    for u in range(33,250):
        d=(4*u+38)//13
        for capd in {2,d,max(2,d-1)}:
            degree=0;ds=[]
            while degree<=u:ds.append(capd);degree+=capd
            r=len(ds);assert r>=2 and u<degree<=u+capd
            assert 13*(degree-u)<=4*(u+r)+30
            ct['independent_uniform_family_crossing_guards']+=1
        for r in range(2,10):
            for d0 in {(4*u+4*r+30)//13+1, u, 2*u-1}:
                for m in range(10):
                    if 4*u+4*r+30<13*d0 and u+1+m*d0<=3*u-2:
                        assert m<=6;ct['independent_six_suffix_reduction_guards']+=1
    deps=['weaker_count_wedge_C_entrance_verification.json','two_factor_complete_entrance_verification.json',
          'triple_subdegree_C_entrance_verification.json','four_subdegree_C_entrance_verification.json',
          'forward_D_single_plateau_verification.json']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    files=['hereditary_strong_late_C_proof.tex','HereditaryStrongLateC.lean','HereditaryStrongLateC.log',
           'audit_hereditary_strong_late_C.py','audit_hereditary_strong_late_C.json',
           'verify_hereditary_strong_late_C.py','joint_rising_differences.tex']+deps
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_HEREDITARY_STRONG_LATE_C_UNRESTRICTED_SORTED_SUFFIX_AND_SIX_FACTOR_REDUCTION',
      new_scoped_reports=24,kernels=kernels(),state_sha256=qa['state_sha256'],QA=qa['counts'],
      independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
      reference_margin='PROVED ALL infinite-BINARY references,arbitrary nonbinaryorder/caps/counts: G_k-phiGprev>=q^2 forALLk>=1. Fullbinarygapintervalinduction plus all-length affine-window atom payment; referenceorder unrestricted.',
      hereditary='PROVED conditional STRONG physical late-C entrance is preserved underEVERYlegal nonbinaryappendt>=lastcapacity,arbitrarylengthsuffix. Newstrictentryforcesoldstrictentry; oldD mode cap givesnewmu<=oldlambda; ordinaryLC and exact subtraction give newmu<=lastordinaryFratio; BOTH inequalities retainALLoldG additive margins needed bynewwindow. Rankzeroatom andt>=3 payconstant1. WholeordinaryLCtail inheritsbyLCconvolution. All clipped/flat/mode-crossing guards retained.',
      seeded_family='PROVED ANY actual1alpha2uV whoseANYnonbinaryprefix hasr>=2,delta>=5,W>=33 and17u+4r+30>=13h hasEVERYactualC atEVERYcurrentN>=FINALnonbinaryW+1,withARBITRARYlater sorted suffix. ALSO allu>=33,1<=delta<=4 seeds strengthened byexact lowgap1/2seeds andOLDgap3/4ordinaryseeds. FINALword needNOTsatisfyANYcountcone; demonstrated by independently reconstructed actual growing-entry witness.',
      uniform_family='PROVED ALLu>=33 and13(maxV-1)<=4u+38: EVERYactualC fromN>=FINALW+1. OnlytheFIRSTprefixdegree>u needobeythiscapbound; arbitrarylarger sorted suffix then allowed. Ifh<=u OLDlateCapplies. Full first-crossing existence/overshoot and2-factor guard kernelchecked.',
      six_suffix_reduction='PROVED forANY possible late-Cfailure withu>=33 andOLDautomaticcomplementh<=3u-2: FIRSTnonbinaryprefixdegree>u mustfailseedcone ifr>=2; AT MOSTSIXnonbinaryfactorsfollowit. Ifcrossingprefixr1,AT MOSTONEfactorfollows. Fullcrossingprefix/binarycountremainUNBOUNDED; thisisNOTafinitecompletedverification. u9..32 remainsseparatefinitebinarycountcomplement; notclaimedclosed.',
      new_coverage_witness=wit,
      formal_scope='TWENTY-FOUR NEW cleanstandardaxiomreports: whole ratio/mode/cumulativeprefix/first-crossing inductions,full finite-sum algebra,all-lengthhead/tailwindowmargin,lowgapordinaryseeds,uniformfamilyandSIXsuffixintegerguards. Actualrecurrence/support/mode/LCconvolution andwholewordassemblyWRITTEN,notend-to-end Lean actualcompositiontheorem. No sampled logical premise; finiteQAonly.',
      remaining='Unseeded first-crossing entrance remains OPEN,asdoearlierC belowphysicaltail/fullA2/originalunamplifiedcoefficientUI. Inheritedhalfline startsFINALW+1; doesNOTclaimFINALWboundary. GeneralfullCfirstunresolvednononecount6unchanged.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'hereditary_strong_late_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()

