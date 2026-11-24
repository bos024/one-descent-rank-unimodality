"""Independent positive boxes, q-basis source identification and true greedy ideals."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_subdegree_CI_entrance import suffix_boxes
from verify_binary_ternary_A2_original_family import boxes,check,core,greedy_ideal,UI
from verify_mixed_three_four_proper_quotient import ci,proper_forward
from audit_renewal_root_primitive_cut import RootField
def reports():
    src=(ROOT/'MixedThreeFourActualCut.lean').read_text();log=(ROOT/'MixedThreeFourActualCut.log').read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==9
    out={}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256();f=RootField(3);b=f.q
    l=f.add(f.one,f.add(b,f.mul(b,b)));a=f.sub(l,f.one);bsum=f.add(f.one,f.add(a,b))
    for s in list(range(0,18))+[22,35,50]:
        for extra in [0,13]:
            r=max(32,3*s+8)+extra;U=[3]*r+[4]*s;P=r+s+2;T=3*r+4*s
            for alpha in [1,2,4,19]:
                F=boxes(alpha,U)+[0,0];G=[];v=0
                for x in F:v+=x;G.append(v)
                d=[max(0,F[n]-F[n-1]) if n>=2 else 0 for n in range(len(F))]
                for n in range(P,len(F)-1):
                    assert F[n]**2>=F[n-1]*F[n+1];ct['independent_actual_ENTIRE_ordinary_tail_minors']+=1
                for N in range(4,len(F)):
                    for k in range(1,N-2):
                        assert G[k]*d[N-1]>=G[k-1]*d[N],(alpha,r,s,N,k)
                        ct['independent_actual_C_ALLcurrent_ALLshift_direct_reads']+=1
                assert f.sign(f.sub(f.scale(l,F[P-1]),f.scale(f.one,F[P])))>0
                assert F.index(max(F))<=T;ct['independent_actual_strictROOTentry_and_MODEguards']+=1
                if s:assert F[5]<16
                ct['independent_actual_positive_box_hosts']+=1
                sha.update(str((alpha,r,s,F[-4:])).encode())
    print(json.dumps(dict(phase='independent_ACTUAL_C_and_ordinary',counts=dict(ct))),flush=True)
    for s,r in [(0,32),(2,32),(8,32),(16,56),(23,77),(36,116)]:
        U=[3]*r+[4]*s;P=r+s+2;Nmax=3*r+4*s+5;E=ci(r,s);Q=proper_forward(f,E)
        R0=f.sub(f.one,Q[0]);R1=f.sub(f.sub(f.scale(f.one,r+s),Q[1]),f.mul(a,Q[0]));Rs=f.add(R0,R1)
        # Independent infinite-padding prefix from positive suffix boxes.
        I=suffix_boxes(Nmax+1,U)[:Nmax+1]
        V=[];v=f.zero
        for j in range(Nmax-P+1):
            if j<len(Q):v=f.add(v,Q[j])
            V.append(f.add(f.mul(bsum,v),Rs))
        cv=0
        for j in range(len(V)):
            if j<len(E):cv+=E[j]
            rhs=V[j]
            if j:rhs=f.add(rhs,f.mul(a,V[j-1]))
            if j>=2:rhs=f.add(rhs,f.mul(b,V[j-2]))
            if j==0:rhs=f.add(rhs,f.sub(f.mul(bsum,R0),Rs))
            if j==1:rhs=f.add(rhs,f.mul(b,Rs))
            assert rhs==f.scale(bsum,cv);ct['independent_TRUE_degreeONE_source_identity_reads']+=1
            if j:
                obs=f.mul(bsum,f.sub(f.scale(l,I[P+j-1]),f.scale(f.one,I[P+j])))
                assert obs==f.add(V[j],V[j-1]);ct['independent_ACTUAL_TWOterm_V_lambda_source_reads']+=1
        for j in range(1,len(V)-1):
            assert f.sign(f.sub(f.mul(V[j],V[j]),f.mul(V[j-1],V[j+1])))>=0;ct['independent_cumulativeQ_GLOBAL_LC_reads']+=1
        for alpha in [1,2,4,17]:
            F=suffix_boxes(alpha,U);ell=alpha-1;cs=[];v=0
            for en in E:v+=en;cs.append(v)
            for j in range(Nmax-P+1):
                k=j-ell;loss=0 if k<0 else cs[min(k,len(cs)-1)]
                assert I[P+j]-loss==(F[P+j] if P+j<len(F) else 0)
                ct['independent_FULLFINITEones_signed_cut_actual_identification_reads']+=1
        ct['independent_actual_cumulative_model_contexts']+=1
    old=[(1,[2]*3+[3]*4),(2,[2]*2+[4]*3),(1,[2]*2+[7,9]),(2,[3]*2+[12])]
    for case in range(36):
        s=1+case%8;r=max(32,3*s+8);alpha=1+case%2;U=[3]*r+[4]*s
        if case%3==0:
            t=1+case%5;rho=max(32,3*t+8);beta=1+(case//2)%2;V=[3]*rho+[4]*t
        else:beta,V=old[case%4]
        A,H=boxes(alpha,U),boxes(beta,V)
        appended=False
        if case%6==0:
            t=max(4,beta+sum(V)-alpha-sum(U),10+case)
            U=U+[t];A=boxes(alpha,U);assert len(A)>=len(H);appended=True
        check(A,H,ct,sha,not appended)
        M=max([1]+U+V)+1+case%3;Pcore,L,R=core(A,H,M)
        host=[1]*alpha+U+[M]+list(reversed([1]*beta+V))
        actual=greedy_ideal(host);assert actual==Pcore and UI(actual)
        ct['independent_TRUE_GREEDY_ORIGINAL_distinct_composition_ideals']+=1
        ct['independent_TRUE_GREEDY_ORIGINAL_rank_counts']+=len(actual)
        ct['independent_ORIGINAL_BOTH_relative_polynomials']+=2
        if appended:ct['independent_TRUE_GREEDY_one_heavier_append_ideals']+=1
        sha.update(str((host,actual,L,R)).encode())
    primary=json.loads((ROOT/'audit_mixed_three_four_surplus_actual.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_ACTUAL_THREE_FOUR_SURPLUS_COMPLETE_C_FULL_A2_AND_ORIGINAL_FAMILY'
    local=['mixed_three_four_surplus_actual_C_original_proof.tex','MixedThreeFourActualCut.lean','MixedThreeFourActualCut.log',
      'audit_mixed_three_four_surplus_actual.py','audit_mixed_three_four_surplus_actual.json','verify_mixed_three_four_surplus_actual.py']
    deps=['mixed_three_four_proper_quotient_verification.json','mixed_three_four_proper_quotient_proof.tex',
      'MixedThreeFourProperQuotient.lean','MixedThreeFourProperQuotient.log','verify_mixed_three_four_proper_quotient.py',
      'infinite_three_four_reference_C_verification.json','infinite_three_four_reference_complete_C_proof.tex','InfiniteThreeFourReference.lean','InfiniteThreeFourReference.log',
      'parameterized_renewal_residual_verification.json','renewal_root_primitive_cut_verification.json','renewal_root_positive_primitive_cut_proof.tex',
      'RenewalRootPrimitiveCut.lean','RenewalRootPrimitiveCut.log','surplus_ordinary_tail_LC_proof.tex','finite_initial_ones_relative_derivative.tex',
      'ordinary_golden_growth_source_proof.tex','ordinary_tail_to_complete_C_proof.tex',
      'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
      'stationary_four_complete_C_verification.json','stationary_four_complete_C_proof.tex',
      'audit_binary_ternary_A2_original_family.py','verify_binary_ternary_A2_original_family.py',
      'verify_subdegree_CI_entrance.py','audit_renewal_root_primitive_cut.py','probe_tribonacci_quadratic_inverse.py','build_tribonacci_rich_reverse_certificate.py']
    out=dict(status='PASS_UNBOUNDED_ACTUAL_THREE_FOUR_SURPLUS_COMPLETE_C_AND_A6_ORIGINAL_UNAMPLIFIED_COEFFICIENT_FAMILY',new_scoped_reports=9,kernels=reports(),
      actual_C='EVERYalpha>=1,s>=0,r>=32and r>=3s+8:ACTUAL1alpha3^r4^s COMPLETEC ALLcurrent/ALLshift. BOTHcounts/paddingunbounded. NOFINITEparameterpremise.',
      ordinary_tail='SAMEactualarms ENTIREordinaryFLCeverycentreN>=r+s+2. ProperQordinaryLC=>correctedCUMULATIVEVgloballyLC/positiveprimitiveAFTER0LC;[2]futuremodel+ALLORDERt3signedcut+degreeONEsource/startups/modeguard. NOprimitiveLCofQassumed.',
      exact_model='E=B3Q+R0+R1z,gamma=(R0+R1)/B3(1),V=Q/(1-z)+gamma/(1-z). TRUEcumulativeE=B3V+T,T=(R0-gamma)+q3gamma*z. Actualinfiniteonesx atoffsetw2 haslambda*xprev-x=[2]V forALLoffsetj>=1;boundedfuturegivesx=[2]future_q V ALLj>=0. NOTidentifiedatj=-1. ALLotherpolynomialsourcecomponentsretainedinKdegreeargument.',
      physical_joins='NEWall-countdampedpaymentn>=3s9=>10*2^s*q3^floor(n/2)<1 via100(6/11)^8<1. Physicalj0 paidDIRECTLYfromreferenceunitminor/TRUEfirstloss1or2/nextlossw3or2w4includingalpha2extra1. ALLsourceell/ell1/ell2 paidwithm1>=4,m2>=4m1,m3>=4m2 andsourceLC;mandatory[2]factoranddegreeONEremainderKEPT.',
      original_A6='A6=A5 UNIONALLbinary/fourarms UNIONNEW1alpha3r4s(r>=32,r>=3s8). EVERYmemberC/kappa<=5,final-deletionclosed sinceallpure3inA5. OLDSHARPkap5criterion=>FULLpairA2/ENTIREpositive-sourceconeforbothnonrect/ORIGINALCOREandBOTHrelativesANYstrictcentralpeak. ONEarbitrarylegalheavierappendalsoallowed. NOAMPLIFICATION. FirstPROVEDwithin-one-armunbounded3/4mixedORIGINALfamilyinthiscontinuation.',
      formal_scope='NINEnewCLEANstandardaxiomSCOPEDreports:wholeallcountnorm/dampedpowercone/gammabox/wholedegreeONEsourceidentity/cumulativeVseed/ALLrealTRUEsourcestartupbudgets/genericsignedstartupminor/physicalfirstactualdefectminor/deletionarithmetic. ALLORDERcut/completecumulativeLCprimitiveinduction/finitepaddingdensity/referenceC/properQ/wholeboundedC/kappa5originalkernelsREUSEDwithoutrecount. Series/degree/futureinverse/constanttaillimits/wholeactualandoriginalassemblyWRITTEN,notendtoendLeancompositions. NOnewfiniteproofpremise.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='PROVED_STATED_TERNARY_SURPLUS_CONE_ONLY',full_mixed_binary_three_four_C='OPEN',
      next='Removeartificialr>=32/ternarysurplusgap,extendactualcutnear r=3s-4 andjoinNEWreferenceordinaryhead+4heredityforoppositecone. Binaryprefixu>=1hasEXTRAcomponentsnotcoveredbythismodel. GeneralunamplifiedoriginalstillOPEN.',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'mixed_three_four_surplus_actual_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
