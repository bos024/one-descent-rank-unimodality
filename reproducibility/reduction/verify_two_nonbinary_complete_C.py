"""Independent positive-box full-C reconstruction and guarded registration."""
from pathlib import Path
import sys,json,hashlib,re
from itertools import accumulate
from random import Random
from collections import Counter
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT if (ROOT/'verify_subdegree_CI_entrance.py').exists() else Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_physical_boundary_golden_C import reference
from audit_arbitrary_Fibonacci_tail_late_C import sign
NAMES=['one_jump_golden_head_bounds','decaying_tail_below_head','exact_window_golden_payment',
 'correct_binary_first_missing','all_small_binary_residuals_excluded','surplus_residual_read_guards',
 'deficit_residual_read_guards','whole_ordinary_LC_prefix_tail_join','all_current_complete_C_assembly']

def kernels():
    src=(ROOT/'TwoNonbinaryCompleteC.lean').read_text();log=(ROOT/'TwoNonbinaryCompleteC.log').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(x in log for x in ('error:','warning:','sorryAx','ofReduceBool','failed'))
    assert log.count('depends on axioms:')==9
    out={}
    for n in NAMES:
        m=re.search(re.escape("'TwoNonbinaryCompleteC."+n+"'")+r' depends on axioms: \[([^]]*)\]',log);assert m,n
        ax={a.strip() for a in m.group(1).split(',') if a.strip()};assert ax<={'propext','Classical.choice','Quot.sound'}
        out[n]=sorted(ax)
    return out

def main():
    qa=json.loads((ROOT/'audit_two_nonbinary_complete_C.json').read_text())
    assert qa['status']=='EXACT_QA_UNBOUNDED_TWO_NONBINARY_COMPLETE_C_UNDER_AUDIT'
    ct=Counter();sha=hashlib.sha256();rng=Random(20261031523)
    def full(F,D):
        G=list(accumulate(F));best=1
        for n in range(4,len(F)):
            k=n-3
            if G[k]*G[best-1]<G[best]*G[k-1]:best=k
            assert G[best]*D[n-1]>=G[best-1]*D[n]
            ct['independent_complete_C_all_current_prefix_minima']+=1
            ct['independent_complete_C_all_shifts_logical_coverage']+=n-3
    def box(alpha,u,V):
        F=suffix_boxes(alpha,[2]*u+V)[:alpha+2*u+sum(V)+1]+[0]
        return F,[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
    for u in range(0,66):
        for L in {3,max(3,u),u+3,2*u+9}:
            for t in {L,L+7}:
                R=reference([L,t],L+t+8)
                rd=[0,0]+[max(0,R[n]-R[n-1]) for n in range(2,len(R))];full(R,rd)
                RR=reference([L],L+t+2)
                for j in range(2,L+1):
                    assert sign((RR[j]-2,1-RR[j-1]))>=0
                    ct['independent_onejump_entire_golden_head_q2_bounds']+=1
                assert sign((1-RR[L],RR[L-1]))>0
                for n in range(t+3,t+L+2):
                    assert rd[n]==R[n]-R[n-1]
                    assert (-rd[n],rd[n-1])==(RR[n-t-1]-RR[n-1],RR[n-2]-RR[n-t-2])
                    assert sign((-rd[n],rd[n-1]))>0
                    ct['independent_exact_TWO_jump_golden_window_payments']+=1
                for alpha in {1,2,u+L+t+2}:
                    O,od=box(alpha,u,[L]);F,D=box(alpha,u,[L,t]);ell=od.index(max(od));K=4;OG=list(accumulate(O))
                    assert 2*ell<=3*u+L+2
                    if L<=4:assert t+K>=L+t
                    elif u<=4:assert ell<=t+K
                    if u>=5 and u<L-1:
                        for j in range(2,len(O)-1):
                            assert O[j]**2>=O[j-1]*O[j+1];ct['independent_GLOBAL_deficit_onejump_ordinary_LC_from2']+=1
                    for n in range(t+5,min(ell,L+t-1)+1):
                        assert u>=5
                        if D[n]<=D[n-1] or not D[n-1]:continue
                        mu=Q(D[n],D[n-1]);assert sign((-mu.numerator,mu.denominator))>0
                        if u>=L-1 and n<=u+3:
                            assert F[:n+1]==R[:n+1];ct['independent_protected_reference_twojump_complete_C']+=1
                            continue
                        assert mu*O[n-2]<=O[n-1]
                        for k in range(1,n-1):
                            v=OG[k]-mu*OG[k-1];assert sign((v.numerator-2*v.denominator,v.denominator))>=0
                            ct['independent_entire_old_G_q2_margin_payments']+=1
                        ct['independent_surplus_residuals' if u>=L-1 else 'independent_deficit_residuals']+=1
                    full(F,D);ct['independent_positive_box_full_actual_hosts']+=1
                    sha.update(json.dumps([alpha,u,L,t,ell,D[L+t-1:L+t+1]],separators=(',',':')).encode())
    for _ in range(170):
        u=rng.randint(0,130);L=rng.randint(3,150);t=rng.randint(L,L+120);alpha=rng.randint(1,3*u+L+t+1)
        F,D=box(alpha,u,[L,t]);full(F,D);ct['independent_positive_box_full_actual_hosts']+=1
    deps=['universal_physical_boundary_C_verification.json','general_one_jump_analytic_C_verification.json',
      'sharp_previous_ordinary_LC_verification.json','surplus_ordinary_tail_LC_verification.json',
      'previous_boundary_C_verification.json','reference_ordinary_golden_prefix_verification.json',
      'hereditary_strong_late_C_verification.json']
    old=['universal_prefix_C_window_transfer.tex','UniversalPrefixCWindowTransfer.lean','UniversalPrefixCWindowTransfer.log',
      'audit_universal_prefix_C_window_transfer.json','forward_positive_difference_centers.tex',
      'ForwardPositiveDifferenceCenters.lean','ForwardPositiveDifferenceCenters.log','audit_forward_positive_difference_centers.json',
      'property_C_five_nonone_arms.tex','C_to_coupled_S_rising_window.tex','zero_head_C_bridge.tex']
    for name in deps:
        dep=json.loads((SOURCE/name).read_text())
        assert dep['status'].startswith('PASS'),name
        for f,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,f
    assert json.loads((SOURCE/'audit_universal_prefix_C_window_transfer.json').read_text())['status']=='PASS_UNIVERSAL_PREFIX_C_WINDOW_TRANSFER'
    assert json.loads((SOURCE/'audit_forward_positive_difference_centers.json').read_text())['status']=='PASS_FORWARD_POSITIVE_DIFFERENCE_CENTERS'
    files=['two_nonbinary_complete_C_proof.tex','TwoNonbinaryCompleteC.lean','TwoNonbinaryCompleteC.log',
      'audit_two_nonbinary_complete_C.py','audit_two_nonbinary_complete_C.json','verify_two_nonbinary_complete_C.py']+deps+old
    def fp(f):return ROOT/f if (ROOT/f).exists() else SOURCE/f
    out=dict(status='PASS_UNBOUNDED_COMPLETE_C_AT_MOST_TWO_NONBINARY_FACTORS',new_scoped_reports=9,kernels=kernels(),
      QA=qa['counts'],independent_counts=dict(ct),independent_state_sha256=sha.hexdigest(),new_finite_entrance_certificates=0,
      theorem='PROVED COMPLETEactualC atEVERYcurrentN/EVERYshiftR>=3 forALL1alpha2u(L,t),alpha>=1,u>=0,3<=L<=t,ALLparametersunbounded. Togetherwitholdbinary/onejump,ALLarmswithAT MOSTTWO nonbinaryfactorshaveFULLC,arbitraryTOTALnononecount.',
      rank_cover='PROVED CORRECTkappa(oldonejump)=4foru>=1,3foru0,soK=4. Oldprefixtransferpaysn<=t+4;oldfirstDmode2ell<=3u+L+2anduniversalCfromWleaveONLYu>=5,t+4<n<W,n<=ell. SURPLUSu>=L-1:protectedTWOjumprefpaysn<=u+3;otherwiseprotectedleft>phi/right<phi+ordinaryLCfromu+2integrateALLGq2gaps. DEFICITu<L-1:binaryCDFprefix+sharpordinarytailgiveGLOBALoldFLCfrom2,endpointsubtractionandALLprefixintegrationpayGq2. Affinewindowatom1closeseveryactualread. No falsebinary-countfirstmissingformulaused.',
      reference='PROVED EVERY infinite-BINARY reference obtainedbyTWO SORTEDarbitraryappends3<=L<=t hasFULLC. OnejumpH_j=q+psi^(j+1)>=q2for2<=j<=L,0<H_L<1,tailpsi^mH_L. TWOjumpgoldenDgapEXACTH_(n-t-1)-H_(n-1)>0for t+3<=n<=W+1. Conditionalprefixn<=t+4ANDoldreferenceCfromW-1coverALLothercurrents. Referenceproofprecedesactualproof,NOcircularfiniteu/actualfullCreferenceassertion.',
      coupled='PROVED anysuchqualifyingarmvsANYoppositeactualarmhasordinaryproductcoefficienttiltP_n/2^nUIandALLdepthBOTH-Frising/nonnegative-currentC-to-Snonrecoverywithusualphysicalguards/OLDweightedA2headretainedforS. ProperzeroheadbridgekeepsitsOWNcount/physicalguards. No generalweightedD/A2/originalUIinference.',
      formal_scope='NINEnewcleanstandardaxiomreportsincludeALLhead/tailgoldenbounds,EXACTwindowpayment,CORRECTfirstmissingkernel,ALLsmallumodeexclusion,BOTHresidualreadguards,FULLordinaryLCprefix-tailjoinandALL-currentpredicateassembly. Actualword/firstmissing/center/conditionalC/reference/Fibonacci/cumulative/coupledidentificationsWRITTENwithregisteredinputs,notend-to-endLeancompositiondatatypeformalization. FiniteQAONLY.',
      remaining='GeneralFULLCwith>=THREE NONBINARYfactors/fullA2/originalunamplifiedcoefficientUIOPEN. FirstunresolvedTOTALnononecount6UNCHANGED;newtheoremCLOSESits2nonbinarysubfamilywithu4andALLu>4.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',maximum_nonbinary_count_fully_closed=2,
      sha256={f:hashlib.sha256(fp(f).read_bytes()).hexdigest() for f in files})
    (ROOT/'two_nonbinary_complete_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('sha256','kernels')}),flush=True)
if __name__=='__main__':main()
