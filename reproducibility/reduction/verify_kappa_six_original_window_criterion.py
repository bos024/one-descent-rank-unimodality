"""Independent actual suffix boxes, signed sums and true original ideals.
All finite checks are QA. The new coefficient criterion has no finite premise.
"""
from pathlib import Path
from collections import Counter
from itertools import product
from random import Random
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,conv,core,greedy_ideal,UI

def at(a,n):return a[n] if 0<=n<len(a) else 0
def signed_window(E,t):return [sum(at(E,n-j) for j in range(t)) for n in range(len(E)+t-1)]
def kernels():
    src=(ROOT/'KappaSixWindowRepair.lean').read_text(encoding='utf8')
    log=(ROOT/'KappaSixWindowRepair.log').read_text(encoding='utf8')
    assert 'native_decide' not in src and not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==9
    out={}
    for n,v in rows:
        a=[x.strip() for x in v.split(',') if x.strip()]
        assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(610730)
    for length in range(1,7):
        for c in product(range(1,5),repeat=length):
            if not UI(c):continue
            for tail in [[0],[-1,0,-1],[-5,-1,0,-3]]:
                E=list(c)+[0,1,1]+tail
                for t in range(3,length+7):
                    W=signed_window(E,t);P=[max(0,x) for x in W]
                    assert UI(P)
                    pos=[n for n,x in enumerate(P) if x>0];assert pos==list(range(pos[-1]+1))
                    ct['independent_complete_small_UI_prefix_repair_windows']+=1
            ct['independent_complete_small_UI_prefixes']+=1
            sha.update(str((c,W)).encode())
    def arm_profile(kind):
        a=rng.randint(1,9);u=rng.randint(0,27)
        if kind==0:V=[3]*rng.randint(0,8)+[4]*rng.randint(0,8)
        elif kind==1:
            V=[3]*rng.randint(0,5)+[4]*rng.randint(0,5)
            V=V+[max(5,2*sum(V))+rng.randint(0,9)]
        else:V=sorted(rng.choices([3,4,5],k=rng.randint(1,6)))
        return a,[2]*u+V
    cases=[(arm_profile(j%3),arm_profile(j//3%3)) for j in range(320)]
    cases += [((1,[2]),(a,[5]*r)) for a in [1,2,11] for r in [4,5,6]]
    for (a,U),(b,V) in cases:
        A,B=boxes(a,U),boxes(b,V);aa,bb=len(A)-1,len(B)-1
        ka=next(n for n in range(1,8) if at(A,n)<2**(n-1))
        kb=next(n for n in range(1,8) if at(B,n)<2**(n-1));assert max(ka,kb)<=6
        p=conv(A[::-1],B[::-1]);D=len(p)-1;E=[2*at(p,n)-at(p,n-1) for n in range(D+3)]
        d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)]
        assert UI([x*2**n for n,x in enumerate(d)])
        special=bb if (a,U)==(1,[2]) and kb==6 else aa if (b,V)==(1,[2]) and ka==6 else None
        if U and V:
            nu=D-p[::-1].index(max(p));exceptions=[]
            for n in range(nu+1,len(E)-1):
                if E[n]>=0 and E[n+1]>E[n]:exceptions.append(n)
            if special is None:assert exceptions==[]
            else:
                assert exceptions==[special-1]
                assert E[special-1:special+5]==[0,1,1,-1,0,-1]
                assert min(E[:special-1])>=1 and UI(E[:special-1]) and nu<=special-3
                ct['independent_ENTIRE_exceptional_source_classifications']+=1
            for t in [3,4,7,19]:
                W=signed_window(E,t);assert UI([max(0,x) for x in W])
                ct['independent_three_or_longer_actual_source_windows']+=1
        t=max(max(U+[2]),bb-aa,2)
        if special is not None:assert t>=3
        X=boxes(a,U+[t]);q=conv(X[::-1],B[::-1]);dd=[max(0,x-at(q,n-1)) for n,x in enumerate(q)]
        assert UI([x*2**n for n,x in enumerate(dd)])
        ct['independent_legal_heavier_append_FULL_A2_pairs']+=1
        ct['independent_actual_kappa_six_FULL_A2_pairs']+=1
        sha.update(str((a,U,b,V,E,dd)).encode())
    # Both dominant last jumps are present. Neither is required to be heavier.
    for j in range(24):
        a,b=1+j%3,1+j%2
        U=[2]*(j%7)+[3]*(1+j%3)+[4]*(1+j%4);V=[2]*(j%5)+[3]*(1+j%4)+[4]*(1+j%3)
        WU=sum(t for t in U if t>=3);WV=sum(t for t in V if t>=3)
        U=U+[max(5,2*WU)+j%3];V=V+[max(5,2*WV)+j%4]
        if j%6==0:
            if a+sum(U)<b+sum(V):a,b,U,V=b,a,V,U
            t=max(U)+1;U=U+[t]
            ct['independent_EXTRA_legal_heavier_append_original_ideals']+=1
        M=max(U+V)+1;X,Y=boxes(a,U),boxes(b,V);H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['independent_TRUE_greedy_BOTH_dominant_ORIGINAL_ideals']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        sha.update(str((host,actual)).encode())
    # The two-window assertion stays false, on the exact frozen actual pair.
    A,B=boxes(1,[2]),boxes(1,[5]*4);p=conv(A[::-1],B[::-1]);E=[2*at(p,n)-at(p,n-1) for n in range(len(p)+2)]
    assert signed_window(E,2)[20:23]==[3,1,2]
    assert not UI([max(0,x) for x in E]) and not UI([max(0,x) for x in signed_window(E,2)])
    local=['kappa_six_legal_window_original_criterion_proof.tex','KappaSixWindowRepair.lean','KappaSixWindowRepair.log',
        'audit_kappa_six_original_window_criterion.py','audit_kappa_six_original_window_criterion.json','verify_kappa_six_original_window_criterion.py']
    deps=['certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
        'binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex','BinaryTernaryA2SourceCone.lean','BinaryTernaryA2SourceCone.log',
        'source_birth_gap_nonrecovery.tex','SourceBirthGapNonrecovery.lean','SourceBirthGapNonrecovery.log',
        'audit_source_birth_gap_complement.json','verify_source_birth_gap_complement.json',
        'C_to_coupled_S_rising_window.tex','agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
        'inductive_signed_window.tex','short_prefix_reflection_join.tex','deficit_cumulative_ratios.tex','signed_kernel_extension.tex','ordinary_rooted_caterpillar_model.tex',
        'complete_capacity_four_verification.json','complete_capacity_four_C_original_proof.tex',
        'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
        'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
        'verify_binary_ternary_A2_original_family.py','audit_joint_structure.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_kappa_six_original_window_criterion.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_KAPPA_SIX_LEGAL_WINDOW_COEFFICIENT_CRITERION'
    out=dict(status='PASS_FIRST_MISSING_SIX_LEGAL_WINDOW_FULL_A2_AND_ORIGINAL_A12_COEFFICIENT_CRITERION',new_scoped_reports=9,kernels=kernels(),
        criterion='ANYfinal-deletionclosedACTUALclasswithFULLC/kappa<=6=>FULLpairA2/ORIGINALstrictCOREandBOTHrelativesANYstrictpeak+ONEarbitrarylegalheavierappend. ENTIRErawsourceUIandTWOwindowUIareNOTclaimedandremainFALSE.',
        sole_exception='ALLpostLASTmodeQfailuresconfinedtooldpairX=(1,2),kappaY6,andEXACTedge b-1->b. ENTIREexceptionalEprefix0..b-2positiveINTEGERUI,min>=1; taildelta>=1,0,1,1,-1,0,-1. No other mixed exception underOLDgap5/C/nonrisingresources.',
        repair='ANYpositiveUIprefixc>=1on0..L,thenE_(L1)=0,E_(L2)=E_(L3)=1,EafterL3<=0:ALLuniformwindows t>=3 haveGLOBALLYUIpositivepart/initialsupport. EntirecriticalTHREEranks+signedtail/clipping/globalNoRev/finiteup-downmodeKERNELchecked. t2FALSEactualwindow3,1,2 retained.',
        legality='InSOLEexception,appendingtoXweight3andnewheavierforces t>=b-3>=12;appendingtokappa6arm sortedforces t>=5. ThusEVERYactualheavierappenduses t>=3,includingarbitraryone-extra-jumpcorollary. Allnormalpairs useOLDwhole-sourceUI.',
        original_A12='A12=A11 UNIONALL1alpha2u3r4sT withT>=max5,2(3r+4s) UNIONmaxcap5/nonbinaryweight<=32 arms. ALLuniformFULLC/firstmissing<=6/finaldeletionclosed. BOTHarmsmayINDEPENDENTLYhaveUNBOUNDEDdominantjumps,NOrelativeweightorder;ORIGINALCORE/BOTHrelativesANYstrictpeak+ONEfurtherlegalheavierappend. NOamplification.',
        formal_scope='NINEnewcleanstandardaxiomSCOPEDkernels:completeownerexception/source-modeidentities/criticalrank/tailclipping/globalpatch/noRevtoWHOLEmode/ALLlegalheavierwindowguard. GenericuniformUIconvolution/actualsourceclassification/oldC-Q/gap5/A1/FULLA2andoriginalmodelassemblyWRITTENusingFROZENoldproofs;NOTendtoendLeancompositions. NOnewfiniteproofpremise;ALLfiniteprofilesQAONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',new_finite_proof_premises=0,
        next='Firstmissing>=7legalwindowrepair/directcoefficientbridgeandgeneralhighercapacityC. kappa6raw-sourcecounterhasbeenBYPASSEDwithACTUALlegalwindow,notfalselyremoved. GeneralgoalNOTcomplete.',
        independent_counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'kappa_six_original_window_criterion_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
