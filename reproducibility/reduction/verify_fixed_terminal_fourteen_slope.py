"""Independent finite-kernel coefficients, suffix-box models and closed actual heads.
All finite actual profiles are QA; the fixed-template theorem is UNBOUNDED.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import prod
from random import Random
from collections import Counter
import json,re,time,hashlib,sys
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,UI
from audit_joint_structure import fastconv
def at(A,n):return A[n] if 0<=n<len(A) else 0
def main():
    start=time.monotonic();ct=Counter();rng=Random(202611021616);sha=hashlib.sha256()
    rho=Q(3,5);b=Q(35,32);q=Q(6125,6144);v=Q(175,192)
    def rel(t):return sum(rho**i for i in range(1,t+1))/b**(t-1)
    Pstar=prod(rel(max(4,i+3)) for i in range(10))
    assert Pstar==rel(4)**2*prod(rel(t) for t in range(5,13))
    margin=b**39-Q(41472,125)*Pstar;assert margin>0
    assert q**16<=Q(20,21) and 10*81*v**80<=1
    assert all((a+1)*Q(20,21)**a<=8 for a in range(20))
    src=(ROOT/'FixedTerminalFourteenSlope.lean').read_text(encoding='utf8')
    log=(ROOT/'FixedTerminalFourteenSlope.log').read_text(encoding='utf8')
    assert not any(x in src for x in ['native_decide','sorry','axiom '])
    assert not any(x in log for x in ['warning:','error:','sorryAx','failed','ofReduceBool'])
    reportrows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(reportrows)==9
    kernels={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in reportrows}
    assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in kernels.values())
    for u in range(2,22):
      for w in range(2,22):
        K=[max(0,min(i+1,u,w,u+w-1-i)) for i in range(u+w-1)]
        assert K==fastconv([1]*u,[1]*w)
        for i,k in enumerate(K):assert k<=i+1 and k*rho**i<=Q(6,5)
        ct['independent_COMPLETE_two_interval_kernels']+=1
        for _ in range(2):
            G=[rng.randrange(10) for _ in range(rng.randrange(1,12))];n=rng.randrange(len(G)+len(K)-1)
            convolution=sum(at(K,i)*at(G,n-i) for i in range(n+1))
            assert rho**n*convolution<=Q(6,5)*sum(x*rho**j for j,x in enumerate(G))
            ct['independent_WHOLE_positive_weighted_convolutions']+=1
    for kappa in [16,17,18,19]:
      for kind in ['minimum','largest_capacity','largest_initial','long_uniform']:
        beta=30*kappa if kind=='largest_initial' else 1
        V=list(range(2,kappa))
        if kind=='largest_capacity':V[-1]+=30*kappa
        if kind=='long_uniform':V=[kappa-1]*(2*kappa+4)
        B=boxes(beta,V);M=beta+sum(t-1 for t in V);big=max([beta]+[t-1 for t in V]);S=min(M//2,M-big)
        G=boxes(beta,V[:-3]);pre=boxes(beta,V[:-1]);w,u,T=V[-3:]
        H=fastconv(fastconv([1]*u,[1]*w),G)
        for m in range(S+1,len(B)+2):
            d=at(B,m)-at(B,m-1);assert m*d<=1<<m
            ct['independent_ALL_actual_signed_slope_reads']+=1
            if M<=2*m:
                assert m-1>u and at(pre,m-1)==at(H,m-3)
                ct['independent_ALL_BULK_vanishing_units_and_kernel_reads']+=1
            elif big==beta:
                zero=boxes(0,V) if m==S+1 else zero
                assert d<=at(zero,m)
                ct['independent_ALL_NONBULK_largest_initial_reads']+=1
            else:
                assert d==at(pre,m-1)-at(pre,m-T-1)<=at(pre,m-1)
                ct['independent_ALL_NONBULK_last_capacity_reads']+=1
        for alpha,U in [(1,[3]*(3*kappa//4)),(2,[2]*(kappa-3))]:
            A=boxes(alpha,U);P=fastconv(A,B);D=len(P)-1;p=P[::-1]
            E=[2*x-at(p,n-1) for n,x in enumerate(p)]+[-p[-1],0]
            d=[max(0,x-at(p,n-1)) for n,x in enumerate(p)];f=[x<<n for n,x in enumerate(d)]
            assert UI(f);ell=f.index(max(f));last=max(n for n,x in enumerate(p) if x==max(p))
            for j in range(2,len(A)+1):
                if at(A,j+1)>at(A,j) or at(B,j+1)<at(B,j):continue
                Tcur=2*at(P,j-1)-3*at(P,j)+at(P,j+1)
                if Tcur<=0:continue
                assert j+1<=S
                ct['independent_POSITIVE_actual_recoveries_inside_strict_head']+=1
                n=D-j
                if n<=last or E[n]<0:continue
                for k in range(min(ell,max(0,j-2))):
                    if p[n]<=p[k] or at(p,n+1)<=p[k+1] or E[n]>E[k]:continue
                    assert Tcur<=E[k+1]-E[k]
                    ct['independent_ALL_proper_CLOSED_mixed_head_payments']+=1
            ct['independent_actual_mixed_pairs']+=1
        sha.update(repr((beta,V,B,S)).encode())
    assert ct['independent_ALL_NONBULK_largest_initial_reads']>0 and ct['independent_ALL_NONBULK_last_capacity_reads']>0
    qa=json.loads((ROOT/'audit_fixed_terminal_fourteen_slope.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_QA_UNBOUNDED_FIXED_TERMINAL_FOURTEEN_SLOPE_THINNESS'
    depname='actual_dyadic_slope_thinness_full_branch_verification.json'
    previous=json.loads((SOURCE/depname).read_text(encoding='utf8'))
    for n,digest in previous['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,n
    local=['fixed_terminal_fourteen_slope_thinness_proof.tex','FixedTerminalFourteenSlope.lean','FixedTerminalFourteenSlope.log',
      'audit_fixed_terminal_fourteen_slope.py','audit_fixed_terminal_fourteen_slope.json',
      'verify_fixed_terminal_fourteen_slope.py','build_fixed_terminal_fourteen_lean.ps1','ActualDyadicSlopeNorm_module_build.log']
    deps=[depname,'actual_dyadic_slope_thinness_and_high_source_mixed_S_proof.tex',
      'ActualDyadicSlopeNorm.lean','ActualDyadicSlopeNorm.log','ActualDyadicSourcePayment.lean','ActualDyadicSourcePayment.log',
      'ordinary_lefschetz_realization.tex','source_birth_gap_nonrecovery.tex','source_curvature_linear_owner.tex',
      'mixed_head_raw_primitive_LC.tex','agent_mixed_strict_head_74.tex','first_defect_mass.tex',
      'first_missing_twelve_original_criterion_verification.json','first_missing_twelve_original_criterion_proof.tex',
      'coupled_source_window_A2_and_kappa_nine_original_proof.tex',
      'verify_binary_ternary_A2_original_family.py','verify_subdegree_CI_entrance.py','audit_joint_structure.py',
      'probe_binary_first_defect_ordinary_tail.py']
    out=dict(status='PASS_UNBOUNDED_FIXED_TERMINAL_FOURTEEN_ACTUAL_SLOPE_AND_KAPPA_SIXTEEN_PLUS_MIXED_CLOSED_S',
      new_scoped_reports=9,kernels=kernels,
      fixed_template='ANYACTUALkappa>=16hasLAST14capacities>=2..15. AbsorbFIRSTterminalpartintounrestrictedprefix;TENmiddlecapacities>=3..12transportENTIREnegative-offsetnormmultiplicatively. LastTHREEcapacities>=13/14/15removeatleast39skeletondegrees. GlobalnormandTENCAPACITYproductenvelopeareUNBOUNDED,NOwordenumerationpremise.',
      sharp_resources='WHOLErelativeS_t(3/5)/b^(t-1)decreasesfrom4,andr3<=r4;TENarbitrarycapacitiesproduct<=P*=r4^2prod(r5..r12). WHOLE16-blockq^16<=20/21and(a+1)(20/21)^a<=8=>m q^m<=128. Everytwo-intervalweightedkernelcoeff<=(i+1)rho^i<=6/5;WHOLEnonnegativeweightedconvolution<=6/5timesfullprefixevaluation. Exact41472/125*P*<=b^39.',
      slope_thinness='ANYactualY/kappa>=16/mainCIdegreeM/largestB/sY=min(floor(M/2),M-B): EVERYm>sY hasm*SIGNEDDeltaFY(m)<=2^m. BULK M<=2m:prefixbeforelastTWOhasdegree>=79=>m-1>secondlastcapacity,soBOTHsourceunitsvanish;DeltaFY_m<=[z^(m-3)][u][w]G. Fullweightedkernel+offsetnorm+39-degreebudget+128blockpay. NONBULKuseslastcapacitystripORlargestinitialzero-seedcomparisonandWHOLElarge-readbase80;O>=92.',
      mixed_closed_S='ENTIREproperMIXED/source-prefixCLOSEDgapSforEVERYrisingoppositekappa>=16. Frozenindexedrawgap+WHOLEdyadicsourceidentity/payment=>positiveTforces(j+1)DeltaFY(j+1)>2^(j+1),hencej+1<=sY. Genuineoppositestricthead/RAWownerprefix/ONEabsolutetermorrelative+1surpluspayALLclosedheads,includingequality;negativebirthunitpaid. NonpositiveTretainsusualOLDnonnegativeheadbudget. NOcapacity/count/weight/paddingcutoff,NOwholeRAWwindowUIclaim.',
      remaining='GeneralMIXEDproper-sourcegapnowONLYrisingoppositekappa13,14,15. Frozenownerbounds=>ownerweight<=287,skeletonD<=143;oppositecouplingstillneeded. GENERALhighercapacityC/bothrisingresource/A2/ORIGINALconjectureOPEN. LatestORIGINALcriterionremainskappa<=12/A18;thismixed-onlytheoremdoesnotaloneextendit.',
      formal_scope='NINEnewstandardaxiomreports:WHOLEoffset-tailcontraction/ALLcapacityrelativeenvelope/WHOLE16powerblock/ALLtwointervalweightedcoeffbounds/WHOLEnonnegativefiniteconvolution/TENarbitrarycapacitytemplateproductincludingexactconstant/ALLsupportanddegreeguards/WHOLElarge-read80/WHOLECauchy-to-bulkpayment. ImportsFROZENActualDyadicSlopeNorm,whoseFOURreportsareNOTrecounted. Actualmodel/staircase/coefficientmatching/CIandproper-headassemblyWRITTENandfrozeninputsreused,NOTendtoendLeanwords. NOFINITEWORDPROOFPREMISE;allactualprofilesQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      exact_template_certificate=dict(numerator=margin.numerator,denominator=margin.denominator),
      independent_counts=dict(ct),primary_QA=qa['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
      local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'fixed_terminal_fourteen_slope_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','exact_template_certificate','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
