"""Independent rational bounds, positive suffix boxes, signed source and proper heads.
All additional profiles are QA ONLY; the new theorem has NO finite word premise.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from random import Random
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,UI
from audit_joint_structure import fastconv
def at(A,n):return A[n] if 0<=n<len(A) else 0
def missing(V):return min([len(V)+2]+[t+len(V)-i for i,t in enumerate(V)])
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','failed','ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==count,(name,len(rows))
    out={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in rows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in out.values())
    return out
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(202611022020)
    rho=Q(3,5);b=Q(35,32);c=Q(3,2);q=b*b/(2*rho);v=b/(2*rho);offset=Q(125,22)
    assert q==Q(6125,6144) and v==Q(175,192)
    constants=[]
    for t in range(2,6):
        S=sum(rho**i for i in range(1,t+1));margin=b**(t-1)-S
        assert margin>=0;constants.append(dict(kind='interval_norm',t=t,numerator=margin.numerator,denominator=margin.denominator))
    for name,margin in [
        ('all_large_capacity_norm',b**5-c),('binary_step_margin',10*(b-Q(24,25))-1-offset/25),
        ('whole_power_block_base',Q(1,2)-q**224),
        ('whole_triangle_base',b**171-2240*c**18),
        ('whole_large_read_base',1-10*101*v**100)]:
        assert margin>=0;constants.append(dict(kind=name,numerator=margin.numerator,denominator=margin.denominator))
    assert 10-offset>=Q(5,2) and offset>=2 and offset*(Q(147,125)-1)==1
    kernels={'ActualDyadicSlopeNorm':reports('ActualDyadicSlopeNorm',4),
      'ActualDyadicSlopePowers':reports('ActualDyadicSlopePowers',4),
      'ActualDyadicSourcePayment':reports('ActualDyadicSourcePayment',6)}
    for K in [20,22,27,35]:
      for case in range(12):
        g=K-2+case%4;V=[max(2,K-g+i) for i in range(g)]
        if case%3==1:V[-1]+=rng.randint(2*K,4*K)
        elif case%3==2:V=[max(t,K-1) for t in V]
        if missing(V)!=K:continue
        beta=1 if case%4 else 3*K;B=boxes(beta,V);M=beta+sum(t-1 for t in V);big=max([beta]+[t-1 for t in V]);S=min(M//2,M-big)
        for m in range(S+1,len(B)+2):
            d=at(B,m)-at(B,m-1);assert m*d<=1<<m
            ct['independent_ALL_actual_signed_slope_reads']+=1
            if M<=2*m:ct['independent_bulk_Cauchy_branch_reads']+=1
            elif big==beta:ct['independent_largest_initial_interval_branch_reads']+=1
            else:ct['independent_largest_last_capacity_branch_reads']+=1
        if len(B)<700:
            value=sum(x*rho**n for n,x in enumerate(B));assert value+offset<=10*b**M
            ct['independent_positive_suffix_FULL_fold_evaluations']+=1
        for alpha,U in [(1,[3]*(3*K//4)),(3,[2]*(K-3)),(1,[2,3,7])]:
            A=boxes(alpha,U);P=fastconv(A,B);D=len(P)-1;p=P[::-1]
            E=[2*x-at(p,n-1) for n,x in enumerate(p)]+[-p[-1],0]
            d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];f=[x<<n for n,x in enumerate(d)]
            assert UI(f);ell=f.index(max(f));last=max(n for n,x in enumerate(p) if x==max(p))
            EB=[0,0]+[2*at(B,n-1)-at(B,n) for n in range(2,len(B)+1)]
            assert min(EB)>=0
            EB_A=fastconv(EB,A)
            for j in range(2,len(A)+1):
                if at(A,j+1)>at(A,j) or at(B,j+1)<at(B,j):continue
                T=2*at(P,j-1)-3*at(P,j)+at(P,j+1)
                C=at(A,j-1)-2*at(A,j)+at(A,j+1)
                assert T==C-(at(EB_A,j+1)-at(EB_A,j))
                ct['independent_EXACT_actual_mixed_source_identities']+=1
                if T<=0:continue
                assert j+1<=S,(K,alpha,U,beta,V,j,S,T)
                ct['independent_POSITIVE_actual_recovery_strict_head_bound']+=1
                n=D-j
                if n<=last or E[n]<0:continue
                for k in range(min(ell,max(0,j-2))):
                    if p[n]<=p[k] or at(p,n+1)<=p[k+1] or E[n]>E[k]:continue
                    assert T<=E[k+1]-E[k]
                    ct['independent_ALL_proper_CLOSED_mixed_head_payments']+=1
                    if E[n]==E[k]:ct['independent_EQUAL_closed_source_payments']+=1
            ct['independent_actual_mixed_pairs']+=1
        sha.update(repr((beta,V,M,big,B,S)).encode())
    qa=json.loads((ROOT/'audit_actual_dyadic_slope_thinness.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_QA_NEW_UNBOUNDED_FIRST_MISSING_TWENTY_ACTUAL_SLOPE_THINNESS'
    local=['actual_dyadic_slope_thinness_and_high_source_mixed_S_proof.tex',
      'ActualDyadicSlopeNorm.lean','ActualDyadicSlopeNorm.log',
      'ActualDyadicSlopePowers.lean','ActualDyadicSlopePowers.log',
      'ActualDyadicSourcePayment.lean','ActualDyadicSourcePayment.log',
      'audit_actual_dyadic_slope_thinness.py','audit_actual_dyadic_slope_thinness.json',
      'verify_actual_dyadic_slope_thinness.py']
    deps=['ordinary_lefschetz_realization.tex','audit_ordinary_lefschetz.py','audit_ordinary_lefschetz.json',
      'source_birth_gap_nonrecovery.tex','source_curvature_linear_owner.tex',
      'source_birth_gap_refinements.tex','arbitrary_source_gap_finite_owner.tex',
      'mixed_head_raw_primitive_LC.tex','MixedHeadRawPrimitiveLC.lean','MixedHeadRawPrimitiveLC.log',
      'agent_mixed_strict_head_74.tex','agent_mixed_strict_head_74_verification.json',
      'ordinary_rooted_caterpillar_model.tex','first_defect_mass.tex',
      'first_missing_twelve_original_criterion_verification.json',
      'first_missing_twelve_original_criterion_proof.tex','coupled_source_kappa_nine_verification.json',
      'coupled_source_window_A2_and_kappa_nine_original_proof.tex',
      'binary_ternary_A2_original_family_proof.tex','C_to_coupled_S_rising_window.tex',
      'agent_bothdeclining_first_birth.tex','agent_half_lc_actual_weak_curvature.tex',
      'verify_binary_ternary_A2_original_family.py','verify_subdegree_CI_entrance.py',
      'audit_joint_structure.py','probe_binary_first_defect_ordinary_tail.py']
    for n in [x for x in deps if x.endswith('_verification.json')]:
        dep=json.loads((SOURCE/n).read_text(encoding='utf8'))
        for name,digest in dep.get('sha256',{}).items():assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==digest,(n,name)
    out=dict(status='PASS_UNBOUNDED_ACTUAL_DYADIC_SLOPE_THINNESS_AND_ALL_KAPPA_TWENTY_PLUS_MIXED_CLOSED_S',
      new_scoped_reports=14,kernels=kernels,
      whole_norm='EVERYformal1^betaV,beta>=0,allorderedORunsortedcapacities>=2: F(3/5)+125/22<=10*(35/32)^M,M=beta+sum(t-1). ENTIREarbitraryappendFOLDkernelchecked;S_t(3/5)<=b^(t-1);t>=3offsetpaysunit,binaryexactmargin97/880. WHOLEtailplus2<=c^n(Fprefix+2)<=10c^n b^Mprefix retainsnegativeoffset.',
      slope_thinness='ANYACTUALY/kappa>=20,mainCIdegreeM/largestdegreeB/stricthead sY=min(floor(M/2),M-B): EVERYm>sY has m*SIGNEDDeltaFY(m)<=2^m. Forcedlastn=kappa-2capacities>=2..n+1=>triangledegree;Cauchybulkuseswholem q^m<=224,2240c^n<=b^triangle(n). Other-degreebranchstripslastlargestcapacityORuseszero-seedpositiveformalwordifinitialintervallargest;wholelarge-read10(j+1)(175/192)^j<=1fromj100. ALLcounts/capacities/padding/weightsunbounded;NOwordenumerationpremise.',
      indexed_source_gap='ANYactualmixedownerh>=2/r>=0/C>0: (j+1)*(2qZ_r-qZ_(r-1))>=4qZ_(r+1). WHOLEr0/r1/r>=2proofusesactualOsequenceHilbertupper/skeletoncenter/count-weightguards. WHOLEsigneddyadicprefixidentity+WHOLEdoubling-subreads+nonnegativefiniteconvolution=>positiveT forces (j+1)DeltaFY(j+1)>2^(j+1). Includesrank-twoCORRECTIONexactly;notanassumedscalarpayment.',
      recovery_head='ANYmixed/source-prefixpositiveQrecoverywithr>=0andrisingoppositekappa>=20=>j+1<=sY. ThisusesACTUALoppositemainM/largestB,retainingcapacitycoupling. ALLproperBOTHwindowheadsk+1<=j-2areinsideACTUALstrictDeltaqY>=1;RAWownersafebeforea. OneheadtermpaysABSOLUTEr<k;frozenRAWrelative+1paysr>=kincludingCLOSEDsourceEQUALITY. Negative-rbirthsusefirstbirthorunitconstanthead.',
      mixed_closed_S='ENTIREproperMIXED/source-prefixCLOSEDgapSprovedforEVERYrisingoppositekappa>=20. PositiveTpaidwithoutC/OLDglobalA2;nonpositiveTusesusualOLDnonnegativeheadbudget. Bothstrictwindows,current0<=E_n<=E_k,correctsourceprefixandownerphaseRETAINED. NoFIRSTHALF/count/capacity/weightrestriction. NOwholeRAWsourcewindowUIclaim.',
      remaining='GeneralMIXEDproper-sourceobstructionnowONLYrisingoppositekappa13..19,afterfrozenmax12resourcesandnewUNBOUNDEDkappa>=20theorem. ForK<=19frozenownerbounda<=24K-73<=383,D<=191;oppositecapacities/paddingstillneedcoupledproof. GENERALhighercapacityC/bothrisingresource,UNRESTRICTEDA2andORIGINALconjectureOPEN.',
      formal_scope='FOURTEENnewstandardaxiomreports:4WHOLEcapacity/fold/seed/tailnorm,4WHOLE224-powerblock/triangle/large-read/bulkpayment,6WHOLEindexedowner-gap/genericsignedprefix/doubling-subreads/completeweighted-sourcebudget/completegap-thinness-recoveryexclusion/unboundeddegreeguards. Actualword-to-Cauchy/first-missing-staircase/Hilbert/CI/headrelativeassemblyWRITTENusingfrozeninputs,NOTendtoendLeancompositions. NOFINITEWORDPROOFPREMISE. IndependentexactconstantsandALLadditionalactualprofilesQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      exact_constant_certificate=constants,independent_counts=dict(ct),primary_QA=qa['counts'],
      independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'actual_dyadic_slope_thinness_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','exact_constant_certificate','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
