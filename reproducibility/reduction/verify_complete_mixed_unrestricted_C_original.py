"""Independent inclusion-exclusion kernels, positive suffixes, full source corrections.
The theorem has NO finite-word proof premise. Additional original ideals are QA.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from collections import Counter
import sys,json,re,time,hashlib
import os
ROOT=Path(os.environ.get('ONE_DESCENT_REPLAY_DIR', Path(__file__).resolve().parent))
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,UI
from audit_joint_structure import fastconv
def at(A,n):return A[n] if 0<=n<len(A) else 0
def binom(n,k):return comb(n,k) if 0<=k<=n else 0
def missing(U):return min([len(U)+2]+[t+len(U)-i for i,t in enumerate(U)])
def suffix_sources(U):
    P=[1];S=[]
    for t in reversed(U):
        if len(S)<len(P):S += [0]*(len(P)-len(S))
        for n,x in enumerate(P):S[n]+=x
        P=fastconv(P,[0]+[1]*t)
    return S,P
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rho=Q(3,5);b=Q(35,32);v=Q(175,192)
    r4=sum(rho**i for i in range(1,5))/b**3
    constants=[b**60-25*30030*rho**16*r4**2,Q(2)**34-100*34**5,
      1-100*v**56,1-200*v**67]
    assert all(x>=0 for x in constants)
    src=(ROOT/'FixedTerminalElevenDensity.lean').read_text(encoding='utf8')
    log=(ROOT/'FixedTerminalElevenDensity.log').read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','failed','ofReduceBool'])
    reportrows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(reportrows)==10
    kernels={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in reportrows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in kernels.values())
    for case in range(20):
        U=[5+(case+i)%8 for i in range(7)];P=[1]
        for t in U:P=fastconv(P,[1]*t)
        shifts=[(sum(t for i,t in enumerate(U) if mask>>i&1),(-1)**mask.bit_count()) for mask in range(128)]
        independent=[sum(sign*binom(n-shift+6,6) for shift,sign in shifts) for n in range(sum(t-1 for t in U)+1)]
        assert independent==P
        for n,x in enumerate(P):assert x<=binom(n+6,6) and x*rho**n<=3003*rho**8
        ct['independent_ALL_inclusion_exclusion_seven_interval_coefficients']+=len(P)
    for K in [13,14,15]:
      profiles=[(1,list(range(2,K))),(1,[K-1]*(K-2)),
        (40*K,list(range(2,K))),(1,list(range(2,K-1))+[40*K]),
        (1,[4]*30+list(range(5,K))),(1,[4]*60+list(range(5,K)))]
      for beta,V in profiles:
        assert missing(V)==K
        B=boxes(beta,V);pre=boxes(beta,V[:-1]);G=boxes(beta,V[:-8]);Sproper,Sprod=suffix_sources(V[-8:-1]);long=fastconv(Sprod,G)
        assert pre==[at(Sproper,n)+at(long,n) for n in range(len(pre))]
        M=beta+sum(t-1 for t in V);big=max([beta]+[t-1 for t in V]);strict=min(M//2,M-big)
        for m in range(strict+1,len(B)+2):
            d=at(B,m)-at(B,m-1);assert 20*d<=1<<m
            ct['independent_ALL_constant_density_reads']+=1
            if M<=2*m:
                full_count=sum(binom(m-2,k) for k in range(6))
                assert at(Sproper,m-1)<=full_count<=m**5 and 100*m**5<=1<<m
                ct['independent_ALL_BULK_FULL_source_sum_and_cutset_bounds']+=1
            elif big==beta:ct['independent_NONBULK_largest_initial_reads']+=1
            else:ct['independent_NONBULK_largest_last_capacity_reads']+=1
        for alpha,U in [(1,[2]*(K+9)),(1,[2]*(3*K)),(2,[2]*(2*K)),(1,[3]*(3*K//4))]:
            A=boxes(alpha,U);a=len(A)-1;Downer=sum(t-1 for t in U);h=len(U)
            P=fastconv(A,B);D=len(P)-1;p=P[::-1]
            E=[2*x-at(p,n-1) for n,x in enumerate(p)]+[-p[-1],0]
            u=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];f=[x<<n for n,x in enumerate(u)]
            assert UI(f);ell=f.index(max(f));last=max(n for n,x in enumerate(p) if x==max(p))
            EB=[0,0]+[2*at(B,s-1)-at(B,s) for s in range(2,len(B)+1)];assert min(EB)>=0
            EA=fastconv(EB,A)
            for j in range(2,a+2):
                if at(A,j+1)>at(A,j) or at(B,j+1)<at(B,j):continue
                T=2*at(P,j-1)-3*at(P,j)+at(P,j+1)
                C=at(A,j-1)-2*at(A,j)+at(A,j+1)
                assert T==C-(at(EA,j+1)-at(EA,j))
                ct['independent_EXACT_actual_mixed_source_identities']+=1
                r=a-j;e=Downer-2*r-2
                if r>=0 and C>0 and j-2>strict and 0<=e and alpha+e+3<=K:
                    assert e<=2*r+2
                    Qowner=at(A,j-1);Rowner=2*at(A,j)-at(A,j+1)
                    assert Qowner<=5*Rowner and 20*(at(B,j+1)-at(B,j))<=1<<(j+1) and T<=0
                    ct['independent_OUTSIDE_head_fifth_raw_gap_source_payments']+=1
                if T<=0:continue
                assert j-2<=strict
                ct['independent_POSITIVE_recovery_proper_head_bounds']+=1
                n=D-j
                if n<=last or E[n]<0:continue
                for k in range(min(ell,max(0,j-2))):
                    if p[n]<=p[k] or at(p,n+1)<=p[k+1] or E[n]>E[k]:continue
                    assert T<=E[k+1]-E[k]
                    ct['independent_ALL_proper_CLOSED_source_payments']+=1
            ct['independent_actual_mixed_pairs']+=1
        sha.update(repr((beta,V,B,Sproper,Sprod,strict)).encode())
    assert ct['independent_NONBULK_largest_initial_reads']>0 and ct['independent_NONBULK_largest_last_capacity_reads']>0
    assert ct['independent_OUTSIDE_head_fifth_raw_gap_source_payments']>0
    qa=json.loads((ROOT/'audit_fixed_terminal_eleven_complete_mixed.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_QA_COMPLETE_MIXED_SOURCE_AND_UNRESTRICTED_FULL_C_ORIGINAL_CRITERION'
    deps=['fixed_terminal_fourteen_slope_verification.json','fixed_terminal_fourteen_slope_thinness_proof.tex',
      'FixedTerminalFourteenSlope.lean','FixedTerminalFourteenSlope.log',
      'actual_dyadic_slope_thinness_full_branch_verification.json','actual_dyadic_slope_thinness_and_high_source_mixed_S_proof.tex',
      'ActualDyadicSlopeNorm.lean','ActualDyadicSlopeNorm.log','ActualDyadicSourcePayment.lean','ActualDyadicSourcePayment.log',
      'first_missing_twelve_original_criterion_verification.json','first_missing_twelve_original_criterion_proof.tex',
      'coupled_source_kappa_nine_verification.json','coupled_source_window_A2_and_kappa_nine_original_proof.tex',
      'source_birth_gap_nonrecovery.tex','source_birth_gap_refinements.tex','source_curvature_linear_owner.tex',
      'arbitrary_source_gap_finite_owner.tex','kappa_nine_source_nonrecovery.tex','ordinary_lefschetz_realization.tex',
      'first_defect_mass.tex','mixed_head_raw_primitive_LC.tex','C_to_coupled_S_rising_window.tex',
      'agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
      'binary_ternary_A2_original_family_proof.tex','binary_ternary_A2_original_family_verification.json',
      'clipped_forward_ratio_frontier.tex','inductive_signed_window.tex','short_prefix_reflection_join.tex',
      'complete_capacity_four_verification.json','complete_capacity_four_C_original_proof.tex',
      'two_nonbinary_complete_C_verification.json','two_nonbinary_complete_C_proof.tex',
      'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
      'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
      'verify_binary_ternary_A2_original_family.py','verify_subdegree_CI_entrance.py','audit_joint_structure.py',
      'probe_binary_first_defect_ordinary_tail.py','audit_first_missing_twelve_original.py']
    for name in [x for x in deps if x.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep.get('sha256',{}).items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    local=['complete_mixed_source_unrestricted_C_original_criterion_proof.tex',
      'FixedTerminalElevenDensity.lean','FixedTerminalElevenDensity.log','audit_fixed_terminal_eleven_complete_mixed.py',
      'audit_fixed_terminal_eleven_complete_mixed.json','verify_complete_mixed_unrestricted_C_original.py',
      'build_fixed_terminal_eleven_lean.ps1','FixedTerminalFourteenSlope_module_build.log','ActualDyadicSourcePayment_module_build.log']
    out=dict(status='PASS_COMPLETE_MIXED_CLOSED_S_AND_UNRESTRICTED_FULL_C_TO_ORIGINAL_A_INFINITY_CRITERION',
      new_scoped_reports=10,kernels=kernels,
      constant_density='ANYACTUALY/kappa>=13,sY=min(floor(M/2),M-largestCIdegree): EVERYm>sY satisfies20*SIGNEDDeltaFY_m<=2^m. Fixedlast11>=2..12;FIRSTabsorbed/TWOmiddle>=3,4offsettransport/lastEIGHTremove60degrees. FULLSEVENsourcecorrectionsretainedandpaidbycutset5-tupleboundm^5andWHOLE100m^5<=2^mfrom34. SEVENintervalkernelcoeff<=binom(i+6,6),WHOLEweightedmaximum3003rho^8=>longdensity<=1/25;source<=1/100,total1/20. NONBULKcaplastO>=56/initialO>=66withALLdecreasingpowers. No count/capacity/padding/weightcutoff or finite word premise.',
      final_three_mixed='ForK13/14/15positiveQrankgeometryD=2r+2+e,h<=D,alpha+e+3<=K,j=alpha+h+r+2+e. Outsideproperstrictheadj-2>sY>=S_K33/39/46=>WHOLEintegerguarde<=2r+2,soh+r+1<=5(r+1). ActualordinaryHilbertandownerphasegiveQ<=5RAW_R. FULLdyadicsourceprefixbudget+20DeltaFY_N<=2^N=>ENTIREsourcepaysC=Q-RAW_R,T<=0. PositiveQthereforej-2<=sY;allproperclosedheadspaidbyabsoluteONEtermorrelative+1surplusinclEQUALITY. Negativebirthpaid. NOexplicitowner/oppositewordenumerationpremise.',
      complete_mixed='The MIXED proper CLOSED S gap is CLOSED at EVERYfirstmissingweight. Frozen>=16theorem,NEW13/14/15proof,frozenANY-ownerK10..12certificate,andlowK4..9absoluteowner-countresourcescoveralloldmax>=13pairs. A one-part rising opposite hasK3 and FIRST-birth d<=2 payment literally requiresnoopposite2-partpremise. Rectangularbasesfrozen. NonpositiveTretainsusualOLDnonnegativeheadbudget. Allproper/current/sourceprefix/ownerphaseguardsretained.',
      unrestricted_criterion='ANYfinal-deletion-closedACTUALFULLCclass,WITHOUTANYfirstmissingbound,hasFULLpairA2andORIGINALUNAMPLIFIEDstrictCORE+BOTHrelativescoefficientsUIatEVERYstrictpeak,plusONEarbitrarylegalappendproducingheavierarmwithoutCofnewarm. Generalcountinduction:FULLC=>A1andbothriseQ;bothnonriseactual;NEWcompleteMIXEDS=>frozenWHOLECLOSED-source-to-FULLwindowA2includingEQUALITY/firstboundary;actualterminalcorrectionaboveNEWfirstmode=>truncation;frozenproperdeletion/lowerpeak/reflectionjoins=>ORIGINALcoefficients. CumulativeLCisNOTusedasasubstitute.',
      original_A_INFINITY='BOTHoriginalarmsmaystartfromANYuniformhereditaryFULLCseed(max4alphabet,atmostTWOarbitrarynonbinaryparts,orfixednonbinaryweight<=32),thenANYFINITEUNBOUNDEDnumberofindependentlychosendominantcapacitiesT_i>=2(W0+sumpreviousT),first>=max5,2W0;initialones/binarycountsunbounded. FrozenuniformdominantCplusseedC=>hereditaryFULLCfamily. ANYstrictpeak+ONEextraarbitrarylegalheavierappend;COREandBOTHrelativesUI. No boundSEVENjumps/firstmissingrestriction/amplification.',
      remaining='GENERALhighercapacityC remainsOPEN,asdoesGENERALoriginalconjecture. CompleteMIXEDSisnowPROVED;alongthisrouteC(oradirectreplacementforitsA1/both-risinguse)isthemainremainingbarrier. TheunrestrictedCcriterionisCONDITIONAL,NOTaproofofCforALLactualarms.',
      formal_scope='TENnewstandardaxiomreports:WHOLEsource-polynomialdyadicbudget/sevenintervalweightedcoefficients/WHOLEpositiveconvolution/UNBOUNDEDtwo-capacityproductand8-capacitydegree60/WHOLEbulkCauchydensity/bothotherdegreepowers/WHOLEK13..15integerguard/fifthRAWgap/COMPLETEconstantsourcepayment/ALLhigh-Kdegreeguards. FrozenNorm/Fixed14/ActualDyadicSourcePaymentimportsNOTrecounted. Actualsourcecutsetinjection,starsbars/word/CI/Hilbert/phase/countinduction/ORIGINALjoinsWRITTENusingfrozenresources,NOTendtoendLeancompositions. NOFINITEWORDPROOFPREMISEforNEW13..15;oldercompleteK10..12certificateexplicitlyreused. Extraactual/TRUEgreedytestsQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      independent_counts=dict(ct),primary_QA=qa['counts'],
      exact_constant_certificate=[dict(numerator=x.numerator,denominator=x.denominator) for x in constants],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'complete_mixed_unrestricted_C_original_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','exact_constant_certificate','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
