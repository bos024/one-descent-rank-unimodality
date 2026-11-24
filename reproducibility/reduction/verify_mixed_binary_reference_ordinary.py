"""Independent suffix-product/Fibonacci counts, exact root signs and originals.
Every finite reconstruction here is QA, NEVER a universal proof premise.
"""
from pathlib import Path
from collections import Counter
from random import Random
from math import prod
import sys,json,hashlib,re,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from audit_joint_structure import fastconv
from verify_mixed_three_four_proper_quotient import ci
from verify_universal_renewal_rounding import closed_G
from verify_binary_ternary_A2_original_family import boxes,greedy_ideal,core,UI
from probe_tribonacci_quadratic_inverse import sign

def at(a,n):return a[n] if 0<=n<len(a) else 0
def fibs(N):
    f=[0,1]
    for n in range(2,N+1):f.append(f[-1]+f[-2])
    return f
def suffix_reference(V,N):
    """Positive sum of individual suffix boxes; no chronological R'=1+S R."""
    z=[0]*(N+1);p=[1]
    for j in range(len(V)):
        for i,v in enumerate(p):
            if i+j<=N:z[i+j]+=v
        p=fastconv(p,[1]*V[-j-1])
    ff=fibs(N+2);h2=ff[1:N+2];full=fastconv(p,h2);w=len(V)
    out=[z[n]+at(full,n-w) for n in range(N+1)]
    return out,p
def c_checks(f,last,ct,literal=False):
    g=[];t=0
    for v in f:t+=v;g.append(t)
    d=[0,0]+[f[n]-f[n-1] for n in range(2,len(f))]
    kmin=1
    for n in range(4,last+1):
        k=n-3
        if g[k]*g[kmin-1]<g[kmin]*g[k-1]:kmin=k
        assert g[kmin]*d[n-1]>=g[kmin-1]*d[n],(n,kmin)
        ct['independent_reference_complete_C_currents']+=1
        if literal:
            for k in range(1,n-2):
                assert g[k]*d[n-1]>=g[k-1]*d[n]
                ct['independent_literal_C_shifts']+=1
def reports():
    src=(ROOT/'MixedBinaryReferenceOrdinary.lean').read_text(encoding='utf8')
    log=(ROOT/'MixedBinaryReferenceOrdinary.log').read_text(encoding='utf8')
    assert 'native_decide' not in src and not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==9
    out={}
    for n,v in rows:
        axioms=[x.strip() for x in v.split(',') if x.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'};out[n]=axioms
    return out
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(281179)
    from audit_mixed_binary_reference_ordinary import reference
    contexts=[(r,s) for r in [57,58,59,63,77,120] for s in [0,1,2,8,16,17,18,19,20,21,30,50,80]]
    contexts += [(rng.randint(57,135),rng.randint(1,88)) for _ in range(90)]
    for r,s in contexts:
        V=[3]*r+[4]*s;W=sum(V);w=r+s;N=W+3;A=w+3
        f,E=suffix_reference(V,N)
        assert E==ci(r,s)
        assert f==reference(V)
        B=[f[n]-at(f,n-1)-at(f,n-2) for n in range(N+1)]
        assert B[W]==1 and B[W+1:]==[0]*3 and min(B)>=0
        ff=fibs(W+5);K=4**r*5**s
        assert f[W]>=K
        for n in range(W-3,W+1):
            assert f[n]**2>=f[n-1]*f[n+1];ct['independent_four_terminal_margins']+=1
        for n in range(A,W+1):
            assert f[n]**2>=f[n-1]*f[n+1];ct['independent_mixed_ordinary_head_minors']+=1
        c_checks(f,W+1,ct,literal=(r==57 and s in [0,1,17,18,30]))
        # Numerator C_s=1+z^4 sum_{j<s}S4^j, constructed from positive boxes.
        C=[0]*(4*s+1);C[0]=1;p=[1]
        for j in range(s):
            for i,v in enumerate(p):C[4+j+i]+=v
            p=fastconv(p,[1]*4)
        h3=[closed_G(3,n)-closed_G(3,n-1) for n in range(N+1)]
        T=fastconv(C,h3)[:N+1]
        losses=[T[A+j]-f[A+j] for j in range(4)]
        expected=[1,w+2,w*(w+1)//2+2*w+5,w*(w+1)*(w+2)//6+w*(w+1)+5*w+11-r]
        assert losses==expected and T[:A]==f[:A]
        for n in range(A,A+3):
            assert T[n]<=2*T[n-1]
            assert T[n]**2-T[n-1]*T[n+1]>=-T[n-1]
            ct['independent_true_startup_unit_minor_payments']+=1
        if A>4*s:
            scalar=(1-(2**s)*h3[r+3],(2**s)*h3[r+2],0)
            assert sign(scalar)>0
            ct['independent_strict_cubic_root_entries']+=1
        else:
            for n in range(s+4,A):
                assert f[n]**2>=f[n-1]*f[n+1]
                ct['independent_four_phase_extension_minors']+=1
        sha.update(str((r,s,f,B,losses)).encode());ct['independent_mixed_reference_contexts']+=1
    for _ in range(160):
        V=[rng.randint(3,24) for _ in range(rng.randint(9,27))];W=sum(V);w=len(V)
        f,E=suffix_reference(V,W+3);B=[f[n]-at(f,n-1)-at(f,n-2) for n in range(W+4)]
        ff=fibs(max(V)+3);K=prod(ff[t-1]+ff[t+1]-1-(-1)**t for t in V)
        assert min(B)>=0 and B[W]==1 and f[W]>=K
        assert w-1<=B[W-1]<=w and 2*B[W-2]>=w*(w-1)
        assert f[W]**2-f[W-1]*f[W+1]==K
        for n in range(W-3,W+1):
            assert f[n]**2>=f[n-1]*f[n+1];ct['independent_arbitrary_order_four_terminal_minors']+=1
        sha.update(str((V,B,f[W-4:],K)).encode());ct['independent_arbitrary_order_words']+=1
    # Positive boxes and a unique greedy leftmost embedding check ORIGINAL ideals.
    for case in range(12):
        r=57+case%3;s=1+case%3;u=2*r+3*s-5+case%2;a=1+case%2
        U=[2]*u+[3]*r+[4]*s
        if case%3==0:
            rr=57;ss=2;vv=2*rr+3*ss-5;V=[2]*vv+[3]*rr+[4]*ss
        elif case%3==1:V=[3]*4+[4]*8
        else:V=[2]*4+[3]*5
        b=1;M=5+case%3;X,Y=boxes(a,U),boxes(b,V)
        H,L,R=core(X,Y,M);host=[1]*a+U+[M]+list(reversed([1]*b+V))
        true=greedy_ideal(host)
        assert H==true and UI(true)
        ct['independent_TRUE_greedy_ORIGINAL_ideals']+=1;ct['independent_TRUE_greedy_rank_counts']+=len(true)
        sha.update(str((host,true)).encode())
    local=['mixed_binary_reference_direct_ordinary_proof.tex','MixedBinaryReferenceOrdinary.lean','MixedBinaryReferenceOrdinary.log',
       'audit_mixed_binary_reference_ordinary.py','audit_mixed_binary_reference_ordinary.json','verify_mixed_binary_reference_ordinary.py',
       'probe_mixed_binary_reference_ordinary_head.py','probe_binary_first_defect_ordinary_tail.py']
    deps=['stationary_ternary_reference_C_verification.json','stationary_ternary_reference_and_binary_dense_C_proof.tex',
       'stationary_four_complete_C_verification.json','stationary_four_complete_C_proof.tex','StationaryFourCompleteC.lean','StationaryFourCompleteC.log',
       'infinite_three_four_reference_C_verification.json','infinite_three_four_reference_complete_C_proof.tex',
       'mixed_three_four_surplus_actual_verification.json','mixed_three_four_surplus_actual_C_original_proof.tex',
       'MixedThreeFourActualCut.lean','MixedThreeFourActualCut.log',
       'three_four_all_four_counts_verification.json','three_four_all_four_counts_actual_C_original_proof.tex','ThreeFourAllFourCounts.lean','ThreeFourAllFourCounts.log',
       'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
       'previous_boundary_C_verification.json','previous_boundary_C_proof.tex','universal_physical_boundary_C_verification.json','universal_physical_boundary_C_proof.tex',
       'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
       'complete_three_four_verification.json','complete_three_four_actual_C_original_proof.tex',
       'verify_binary_ternary_A2_original_family.py','verify_mixed_three_four_proper_quotient.py','verify_universal_renewal_rounding.py',
       'probe_tribonacci_quadratic_inverse.py','audit_joint_structure.py']
    kernels=reports()
    for n in [x for x in deps if x.endswith('_verification.json')]:
        dep=json.loads((SOURCE/n).read_text(encoding='utf8'))
        for f,digest in dep['sha256'].items():
            assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==digest,(n,f)
    primary=json.loads((ROOT/'audit_mixed_binary_reference_ordinary.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_MIXED_BINARY_REFERENCE_DIRECT_ORDINARY_AND_DENSE_ORIGINAL'
    out=dict(status='PASS_ALL_FOUR_COUNTS_MIXED_BINARY_REFERENCE_FROM_FIFTY_SEVEN_THREES_AND_DENSE_A9_ORIGINAL',
       new_scoped_reports=9,kernels=kernels,
       terminal='ANYorderedwordV>=3withw>=9:infiniteBINARYreferenceORDINARYLCatALLFOURcentresW-3..W. CompleteBtop/Cassini/massboundretained;NOsortednessorcount-ratio/finitepremise.',
       reference='EVERYr>=57andEVERYs>=0:infiniteBINARYreferenceR(r,s) FULLC ALLcurrent/ALLshift. OrdinaryLCfromr+s+3throughW=3r+4s;ifr+3<=3s,earlierfroms+4throughW. NOcount-ratio/finiteentrancepremise.',
       true_source='T_s-R(r,s)=z^(r+s+3)[3]^r[4]^s/(P2P3);FOURlossjets1,w+2,w(w+1)/2+2w+5,C(w+2,3)+w(w+1)+5w+11-r. THREEleftminors+middleordinarywindow+FOURuniversalterminalminors coverWHOLEsinduction. Head/tailphysicalguardretained;goldenresidualLCNOTassumed.',
       actual='EVERYalpha>=1,r>=57,s>=0,u>=2r+3s-5:ACTUAL1alpha2u3r4s FULLC ALLcurrent/ALLshift. OneedgeAFTERfirstbinarydefectpaidwithtrue2lossjetsandclipping;thenprotectedbandjoinsOLDactualCfromW-1. ALLu/r/s/paddingunboundedinstatedcone.',
       original_A9='A9=A8 UNIONnewdensemixedarms(r>=57,u>=2r+3s-5),finaldeletionclosed/C/kappa<=5. OLDSHARPcriterion=>FULLpairA2/ENTIREsourceconeBOTHnonrect/ORIGINALstrictCOREandBOTHrelativesANYstrictpeak+ONElegalheavierappend. NOamplification.',
       formal_scope='NINEnewcleanstandardaxiomSCOPEDreports:allFOURterminalscalarminors/exactCassiniidentity/THREEsourcebudgets/completefarnearANDphysicalreadcovers/densejoin/onepostdefectCpaymentWITHclipping. Rootdamping/LCconvolution/ordinaryCbridge/oldwordCassini/actualoriginalmodelassemblyWRITTENusingFROZENoldinputs;NOTendtoendLeancompositions. NOnewfiniteproofpremise;ALLfinitehostsQAONLY.',
       general_original='OPEN',general_C='OPEN',general_A2='OPEN',full_mixed_binary_three_four_C='OPEN',new_finite_proof_premises=0,
       next='Completeinfinitebinarymixedreferenceatsmallr<57;thenarbitraryshorterbinaryprefixes/generalcapacitiesandbeyondkappa5originalbridge. GeneralgoalNOTcomplete.',
       counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
       local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'mixed_binary_reference_ordinary_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
