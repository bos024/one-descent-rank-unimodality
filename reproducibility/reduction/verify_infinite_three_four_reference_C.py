"""Independent closed bounded-composition numerator and q-basis norm reconstruction."""
from pathlib import Path
from math import comb
from collections import Counter
import sys,json,time,hashlib,re,ast
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_universal_renewal_rounding import closed_G
from audit_renewal_root_primitive_cut import RootField

def bounded4(k,n):
    if k==0:return int(n==0)
    if n<0:return 0
    return sum((-1)**j*comb(k,j)*comb(n-4*j+k-1,k-1) for j in range(min(k,n//4)+1))
def closed_reference(s,N):
    C=[int(n==0)+sum(bounded4(k,n-4-k) for k in range(s)) for n in range(N+1)]
    h=[closed_G(3,n)-closed_G(3,n-1) for n in range(N+1)]
    F=[sum(C[i]*h[n-i] for i in range(n+1)) for n in range(N+1)]
    return C,F,h
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text();log=(ROOT/(name+'.log')).read_text()
    assert not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed']) and 'native_decide' not in src
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    zero=re.findall(r"'([^']+)' does not depend on any axioms",log)
    assert len(rows)+len(zero)==count
    out={n:[] for n in zero}
    for n,raw in rows:
        ax=[s.strip() for s in raw.split(',') if s.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};out[n]=ax
    return out
def main():
    st=time.monotonic();ct=Counter();sha=hashlib.sha256()
    data=json.loads((ROOT/'infinite_three_four_reference_base_data.json').read_text());bases=[];boundaries=[]
    for row in data['contexts']:
        s=row['s'];C,F,h=closed_reference(s,4*s+1)
        assert F==row['F']
        minors=[F[n]**2-F[n-1]*F[n+1] for n in range(s+4,4*s-1)]
        assert minors==row['minors'] and min(minors,default=0)>=0
        bases+=minors;ct['independent_COMPLETEfinite_base_contexts']+=1;ct['independent_COMPLETEfinite_base_ordinary_minors']+=len(minors)
        if s<=2:
            G=[];v=0
            for x in F:v+=x;G.append(v)
            N=4*s;k=N-3
            boundaries.append((F[N-1]-F[N-2])*G[k]-(F[N]-F[N-1])*G[k-1])
    assert len(bases)==651 and boundaries==data['one_unit_cumulative_boundaries']==[0,40]
    src=(ROOT/'InfiniteThreeFourReferenceBase.lean').read_text()
    chunks=[ast.literal_eval(x) for x in re.findall(r'def chunk\d+ : List ℤ := (\[[^\n]+\])',src)]
    assert [v for c in chunks for v in c]==bases and len(chunks)==5
    extra=ast.literal_eval(re.search(r'def boundaryAndGrowth : List ℤ := (\[[^\n]+\])',src).group(1))
    assert extra==[0,40,1,0,3]
    for s in list(range(0,51))+[65,85,120]:
        W=4*s;Nmax=W+55;C,F,h=closed_reference(s,Nmax)
        G=[];v=0
        for x in F:v+=x;G.append(v)
        D=[F[n]-(F[n-1] if n else 0) for n in range(len(F))]
        if s:
            a=2**s;c=(a-1)*(a-2)//6
            for n in range(W-3,Nmax+1):
                assert G[n]==a*closed_G(3,n-s)-c;ct['independent_closed_CDF_tail_reads']+=1
            assert G[W-4]==a*closed_G(3,3*s-4)-c+1;ct['independent_EXTRA_UNIT_cumulative_joins']+=1
            for n in range(s+4,W-1):
                assert F[n]**2>=F[n-1]*F[n+1];ct['independent_whole_ordinary_reference_heads']+=1
            if s>=22:
                for n in range(3*s-5,Nmax-1):
                    assert a*abs(h[n]**2-h[n-1]*h[n+1])<=h[n-1]
                    ct['independent_scaled_closed_count_minor_cone_reads']+=1
        for n in range(1,Nmax):
            assert G[n]**2>=G[n-1]*G[n+1];ct['independent_GLOBAL_CDF_LC_reads']+=1
        for N in range(4,Nmax+1):
            for k in range(1,N-2):
                assert G[k]*D[N-1]>=G[k-1]*D[N],(s,N,k)
                ct['independent_ALLcurrent_ALLshift_reference_C_reads']+=1
        sha.update(str((s,C[:W+1],F[-3:],G[-3:])).encode())
    # Different exact basis: q, with q^3+q^2+q=1, instead of lambda.
    f=RootField(3);q=f.q;l=f.add(f.one,f.add(q,f.mul(q,q)));a=f.sub(l,f.one)
    h=[closed_G(3,n)-closed_G(3,n-1) for n in range(201)]
    e=[f.sub(f.scale(f.one,h[n]),f.scale(l,h[n-1] if n else 0)) for n in range(len(h))]
    bn=f.one;bound=f.one
    for n in range(1,len(h)):
        bn=f.mul(bn,q)
        norm=f.add(f.add(f.mul(e[n],e[n]),f.mul(a,f.mul(e[n],e[n-1]))),f.mul(q,f.mul(e[n-1],e[n-1])))
        assert norm==bn;ct['independent_qbasis_ENTIREnorm_QA_reads']+=1
        bound=f.power(n//2)
        assert f.sign(f.sub(f.scale(bound,2),e[n]))>=0 and f.sign(f.add(f.scale(bound,2),e[n]))>=0
        ct['independent_qbasis_absolute_residual_envelope_reads']+=1
    primary=json.loads((ROOT/'audit_infinite_three_four_reference_C.json').read_text())
    assert primary['status']=='EXACT_QA_PASS_INFINITE_THREE_FOUR_REFERENCE_COMPLETE_C_AND_GLOBAL_CDF_LC'
    local=['infinite_three_four_reference_complete_C_proof.tex','InfiniteThreeFourReference.lean','InfiniteThreeFourReference.log',
      'InfiniteThreeFourReferenceBase.lean','InfiniteThreeFourReferenceBase.log','build_infinite_three_four_reference_base.py',
      'infinite_three_four_reference_base_data.json','audit_infinite_three_four_reference_C.py','audit_infinite_three_four_reference_C.json',
      'verify_infinite_three_four_reference_C.py']
    deps=['stationary_four_complete_C_verification.json','StationaryFourCompleteC.lean','StationaryFourCompleteC.log',
      'universal_polynacci_minor_bounds_verification.json','parameterized_renewal_residual_verification.json',
      'universal_renewal_rounding_verification.json','ordinary_tail_to_complete_C_proof.tex','first_missing_renewal_envelope.tex',
      'FirstMissingRenewalEnvelope.lean','FirstMissingRenewalEnvelope.log','verify_universal_renewal_rounding.py',
      'audit_renewal_root_primitive_cut.py','verify_renewal_root_primitive_cut.py']
    out=dict(status='PASS_ALL_COUNT_INFINITE_THREE_FOUR_REFERENCE_COMPLETE_C_GLOBAL_CDF_LC_AND_ORDINARY_PHYSICAL_HEAD',new_scoped_reports=16,
      kernels=dict(InfiniteThreeFourReference=reports('InfiniteThreeFourReference',15),InfiniteThreeFourReferenceBase=reports('InfiniteThreeFourReferenceBase',1)),
      full_C='EVERYs>=0,R_s=sum_i<s S4^i+S4^s/P3 hasFULLC ALLcurrentN>=4/ALL1<=k<=N-3. No count/rank/shiftbound. INFINITEreference,NOTallfiniteactual3/4arms.',
      global_CDF='EVERYs>=0,ordinaryforwardCDF G_s GLOBALLYLC. HeadusesprovedORDINARYFLCandstrictroot4entry;tailG=aG3-c_s withG3LC/convex,c_s>=0. ThisCDFtheoremNOTanoriginalcoefficientUIconclusion.',
      ordinary_head='EVERYs>=1,ordinaryR_s LC EVERYcentre s+4<=n<=4s-2. FIRSTh4lossONEats4. Whole4convolutionheredity:THREEstartupbudgetsREUSED,ALLmiddletruncationreadsandFOURsignedtailcornersPAID. GoldenresidualHphiheadLCisFALSEandNOTused.',
      damped_norm='EXACTternaryresidual e_n^2+(lambda3-1)e_neprev+q3*eprev^2=q3^n. Coercivity=>ABS(e_n)<=2q3^floor(n/2);ABS(M_h3(n))<=10*hprev*q3^floor(n/2). ALLs>=22/n>=3s-5:2^sABS(M_h3(n))<=hprev via6400(2/3)^s<1. ENTIREnatural-index/floor/powerproof.',
      exact_joins='WHOLES4=2z-zP3;R_s=2^sz^s*h3+J_s,degJ=4s-3,top-1. FOURlastnegativeJcoeffs1,s-2,C(s-1,2),C(s,3)+2RETAINED. Gtail=aG3-c_s,c_s=(2^s-1)(2^s-2)/6. AtN=W CpreviousCDFhasEXTRA+1;newc_s>=3and3/2D_h3growthpaysitALLs>=3. s1,2boundaryminors0,40KERNELchecked.',
      finite_entrance='COMPLETEs1..22physicalordinaryheads:651EXACTinteger minors,5chunksONEaggregateAXIOMFREE. Plusboundaryminors0,40andthreegrowthseeds1,0,3. s22fixedbaseforWHOLEsinduction;notunboundeddiagonalassumption.',
      formal_scope='FIFTEENnewcleanstandardaxiomSCOPEDgeneric/root/CommRing/Naturalinductionreports+ONEaxiomfreeCOMPLETEfinitebaseaggregate. Priorordinary4startup/strictunitrounding/wholeboundedordinary-CandreferenceCDF/CkernelsREUSEDwithoutrecount. Model/tailcoefficientidentification/LCconvolution/wholeCassemblyWRITTEN,notendtoendLeancompositionformalization. AdditionalparameterQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',mixed_three_four_single_arm_C='OPEN',
      next='Retainnegativefinite3countCIcorrection. Candidateactualordinarytailcone:r<=3s-2froms4;oppositefromr+s2;UNPROVED. Root3properquadraticquotientLCnormcone4^s*q3^r shouldsupplylateordinaryactualbridge. DoNOTdiscardOTHERsourcecomponents.',
      counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-st,
      local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'infinite_three_four_reference_C_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['sha256','kernels']}),flush=True)
if __name__=='__main__':main()
