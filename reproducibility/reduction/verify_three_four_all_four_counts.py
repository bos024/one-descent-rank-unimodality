"""Independent actual suffix boxes, exact root entries and true greedy originals."""
from pathlib import Path
from collections import Counter
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,check,core,greedy_ideal,UI
from verify_universal_renewal_rounding import closed_G
from audit_renewal_root_primitive_cut import RootField
def reports():
    src=(ROOT/'ThreeFourAllFourCounts.lean').read_text();log=(ROOT/'ThreeFourAllFourCounts.log').read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==4
    out={}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    roots={}
    for t in [3,4]:
        f=RootField(t);l=f.zero
        for j in range(t):l=f.add(l,f.power(j))
        roots[t]=(f,l)
    for r in [50,51,52,57,70,95]:
        s0=(r+4)//3
        for s in [0,1,5,17,18,19,25,50,90]:
            U=[3]*r+[4]*s
            for alpha in [1,2,4]:
                F=boxes(alpha,U)+[0,0];G=[];v=0
                for x in F:v+=x;G.append(v)
                d=[max(0,F[n]-F[n-1]) if n>=2 else 0 for n in range(len(F))]
                starts=[]
                if r+4>=3*s:starts.append(('near',r+s+2))
                if s>=s0:starts.append(('four',s+4))
                for kind,A in starts:
                    for n in range(A,len(F)-1):
                        assert F[n]**2>=F[n-1]*F[n+1];ct['independent_'+kind+'_ENTIRE_ordinary_tail_minors']+=1
                if s>=s0:
                    A=s+4;f,l=roots[4]
                    assert F[A]==closed_G(4,A)-closed_G(4,A-1)-1
                    assert f.sign(f.sub(f.scale(l,F[A-1]),f.scale(f.one,F[A])))>0
                    ct['independent_FOURroot_TRUEfirstdefect_strict_entries']+=1
                if r+3>=3*s:
                    A=r+s+2;f,l=roots[3]
                    assert f.sign(f.sub(f.scale(l,F[A-1]),f.scale(f.one,F[A])))>0
                    ct['independent_THREEroot_strict_entries']+=1
                for N in range(4,len(F)):
                    for k in range(1,N-2):
                        assert G[k]*d[N-1]>=G[k-1]*d[N],(alpha,r,s,N,k)
                        ct['independent_ALLcurrent_ALLshift_ACTUAL_C_direct_reads']+=1
                ct['independent_ALLfour_count_actual_hosts']+=1
                sha.update(str((alpha,r,s,F[-3:])).encode())
    # Independently check the moving, UNBOUNDED-ANALYTIC entrance's finite QA instances.
    for r in range(50,87):
        s=(r+4)//3;A3=r+s+2;W=4*s
        assert A3 in [W-2,W-1,W]
        for alpha in [1,2,5]:
            F=boxes(alpha,[3]*r+[4]*s)+[0,0]
            for n in range(s+4,len(F)-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['independent_MOVINGseed_ENTIRE_ordinary_tail_minors']+=1
            assert F[A3-1]**2>=F[A3-2]*F[A3]
            ct['independent_MOVINGseed_ALLthree_diagonal_joins']+=1
    old=[(1,[2]*3+[3]*4),(2,[2]*2+[4]*5),(1,[2]*2+[7,9]),(1,[3]*32+[4]*3)]
    for case in range(30):
        r=50+case%3;s=[1,18,30,50,80][case%5];alpha=1+case%2;U=[3]*r+[4]*s
        if case%4==0:beta=1;V=[3]*51+[4]*20
        else:beta,V=old[case%4]
        appended=False
        if case%7==0:
            t=max(4,beta+sum(V)-alpha-sum(U),12+case);U=U+[t];appended=True
        F,H=boxes(alpha,U),boxes(beta,V)
        if appended:assert len(F)>=len(H)
        check(F,H,ct,sha,not appended)
        M=max(U+V+[1])+1;C,L,R=core(F,H,M)
        host=[1]*alpha+U+[M]+list(reversed([1]*beta+V));actual=greedy_ideal(host)
        assert actual==C and UI(actual)
        ct['independent_TRUE_GREEDY_A7_ORIGINAL_ideals']+=1;ct['independent_TRUE_GREEDY_A7_ORIGINAL_rank_counts']+=len(actual)
        ct['independent_A7_BOTH_relative_polynomials']+=2
        if appended:ct['independent_TRUE_GREEDY_A7_heavier_append_ideals']+=1
        sha.update(str((host,actual,L,R)).encode())
    primary=json.loads((ROOT/'audit_three_four_all_four_counts.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_ALL_ALPHA_ALL_FOUR_COUNTS_AT_THREE_COUNT_AT_LEAST_FIFTY'
    local=['three_four_all_four_counts_actual_C_original_proof.tex','ThreeFourAllFourCounts.lean','ThreeFourAllFourCounts.log',
      'audit_three_four_all_four_counts.py','audit_three_four_all_four_counts.json','verify_three_four_all_four_counts.py']
    deps=['mixed_three_four_surplus_actual_verification.json','mixed_three_four_surplus_actual_C_original_proof.tex','MixedThreeFourActualCut.lean','MixedThreeFourActualCut.log',
      'mixed_three_four_proper_quotient_verification.json','mixed_three_four_proper_quotient_proof.tex',
      'infinite_three_four_reference_C_verification.json','infinite_three_four_reference_complete_C_proof.tex','InfiniteThreeFourReference.lean','InfiniteThreeFourReference.log',
      'StationaryFourCompleteC.lean','StationaryFourCompleteC.log','stationary_four_complete_C_proof.tex',
      'universal_renewal_rounding_verification.json','universal_renewal_rounding_and_ordinary_C_bridge_proof.tex',
      'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
      'audit_binary_ternary_A2_original_family.py','verify_binary_ternary_A2_original_family.py','verify_subdegree_CI_entrance.py',
      'verify_universal_renewal_rounding.py','audit_renewal_root_primitive_cut.py']
    out=dict(status='PASS_ACTUAL_THREE_COUNT_AT_LEAST_FIFTY_WITH_ALL_FOUR_COUNTS_COMPLETE_C_AND_A7_ORIGINAL_FAMILY',new_scoped_reports=4,kernels=reports(),
      actual_C='EVERYalpha>=1,EVERYr>=50,EVERYs>=0:ACTUAL1alpha3r4s FULLC ALLcurrent/ALLshift. NO3/4count-ratio condition. Generalr<50/binaryprefixoutsideprovedclassremainOPEN.',
      ordinary_phases='s0=ceil((r+2)/3). ALLs>=s0 ordinaryFLCENTIREfroms+4;ANYr+4>=3s ordinaryFLCENTIREfromr+s+2. Bothcounts/paddingunbounded. WholephasecovergivesC EVERYs.',
      analytic_seed='MOVINGs0=(r+4)//3>=18,r=3s0-4/-3/-2. NEWnearactualcutgivesordinarytailfromA3=W-2/W-1/W;NEWreferenceordinaryheadcoverspriorband. ONLYW-1joinoutsideheadispaidbycompulsoryNEXTlossdelta>=1andNEWnearunitminor. UNBOUNDEDdiagonalprovedANALYTICALLY,notfinitepremise.',
      near_payment='ALLS>=18/3S<=n+2:10*2^S*b^floor(n/2)<1 via800(2/3)^S<1,b³>=1/8. S=max(s,18)ensuresproperquotientnormandactualunitminorforallr>=50/r+4>=3s. CurrentA=W-2usesPROVEDreferenceLCinstead ofhomogeneousformula;rootentryONLYr+3>=3s. ALLlowboundaryreadsretained.',
      four_heredity='Fixedr>=50 seedF1alpha3r agreesh3through7 EVERYalpha;FIRSTh4loss4 andFOURlossesEXACT1,2,5,12. THREEoldgenericstartups+unitminor/growth+ENTIREoldLCtailuniformconvolution proveheredityALLs>=s0. Noalphabet-binarypremise. Universalh4firstdefectCcriterioncoversfourphase;nearreferenceC/root3entrycoverss<s0.',
      original_A7='A7=A6 UNIONALL1alpha3r4s(r>=50,ALLs). C/kappa<=5/finaldeletionclosed=>FULLpairA2/ENTIREsourcepositivecone/ORIGINALstrictCOREandBOTHrelativesANYstrictpeak+ONEarbitraryheavierappend. WithinONEarm3/4bothunbounded,NOsurplusratio. NOamplification.',
      formal_scope='FOURnewcleanstandardaxiomSCOPEDreports:ENTIREnearboundaryfloor/exponentpayment/ENTIREanalyticdiagonalmaxphasecover/wholecountnorm-and-tiltmonotonicity/exactNEXT-onlyfirstdefectjoin. AllQ/cumulativecut/physicalsource/mode/4startups/referenceC/firstdefectC/kappa5originalkernelsREUSEDwithoutrecount. Model/LCconvolution/wholeunboundedphaseandoriginalassemblyWRITTEN,notendtoendLeancompositions. NOnewfiniteproofpremise.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='PROVED_ALLs_WHEN_r_GE50_PLUS_OLD_CONE',full_mixed_binary_three_four_C='OPEN',
      next='Removefinitefirstcountthresholdr<50withcomplete4entrances/paddingclamp andfiniteexceptionalnear-C certificates. Binaryprefixu>=1 retainsEXTRAsources. GeneralunamplifiedoriginalstillOPEN.',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'three_four_all_four_counts_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
