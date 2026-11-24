"""Independent positive boxes/seed jets and TRUE original composition counts.
No bounded diagnostic is an unbounded proof premise.
"""
from pathlib import Path
from collections import Counter
from random import Random
import sys,json,time,hashlib,re
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_binary_ternary_A2_original_family import boxes,core,greedy_ideal,UI
from verify_mixed_binary_reference_ordinary import suffix_reference
from verify_universal_renewal_rounding import closed_G
from audit_joint_structure import fastconv

def at(a,n):return a[n] if 0<=n<len(a) else 0
def complete_C(f,ct,literal=False):
    G=[];v=0
    for x in f:v+=x;G.append(v)
    D=[0,0]+[max(0,f[n]-f[n-1]) for n in range(2,len(f))];idx=1
    for n in range(4,len(f)):
        k=n-3
        if G[k]*G[idx-1]<G[idx]*G[k-1]:idx=k
        assert G[idx]*D[n-1]>=G[idx-1]*D[n]
        ct['independent_complete_C_currents']+=1
        if literal:
            for k in range(1,n-2):
                assert G[k]*D[n-1]>=G[k-1]*D[n]
                ct['independent_literal_C_shifts']+=1
def kernels():
    src=(ROOT/'MixedBinaryAllCounts.lean').read_text(encoding='utf8')
    log=(ROOT/'MixedBinaryAllCounts.log').read_text(encoding='utf8')
    assert 'native_decide' not in src and not any(x in log for x in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==4
    out={}
    for n,v in rows:
        a=[x.strip() for x in v.split(',') if x.strip()]
        assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def main():
    start=time.monotonic();ct=Counter();sha=hashlib.sha256();rng=Random(711904)
    contexts=[]
    for r in [57,58,60,78]:
        for u in [1,2,3,7,2*r-1,2*r,2*r+1,2*r+2,2*r+4,3*r+5]:
            s0=0 if u<=2*r else (u-2*r)//3+1
            for s in sorted(set([0,1,8,17,18,25,s0,max(0,s0-1),s0+1])):
                contexts.append((rng.choice([1,2,3,15]),u,r,s))
    for a,u,r,s in contexts:
        V=[3]*r+[4]*s;U=[2]*u+V;h=2*r+3*s;W=3*r+4*s;A=r+s+3;w=r+s
        f=boxes(a,U);complete_C(f,ct,literal=(a==1 and u<=2 and s in [1,18]))
        if u<=h:
            for n in range(A,len(f)-1):
                assert f[n]**2>=f[n-1]*f[n+1];ct['independent_ENTIRE_ordinary_tail_minors']+=1
        else:
            assert f[W+1]**2-f[W]*f[W+2]==-(4**r)*(5**s)
            ct['independent_exact_negative_Cassini_controls']+=1
        seed=boxes(a,[2]*u);hc=[closed_G(3,n)-closed_G(3,n-1) for n in range(7)]
        aa,b,c,d=[hc[n]-at(seed,n) for n in range(3,7)]
        assert aa>=1 and b>=2 and c>=5 and d>=11
        jets=[aa,w*aa+b,w*(w+1)//2*aa+w*b+c,
            (w*(w+1)*(w+2)//6-r)*aa+w*(w+1)//2*b+w*c+d]
        assert jets[1]>=4*aa+1 and jets[2]>=4*jets[1]+1 and jets[3]>=4*jets[2]+1
        C=[0]*(4*s+1);C[0]=1;p=[1]
        for j in range(s):
            for i,v in enumerate(p):C[4+j+i]+=v
            p=fastconv(p,[1]*4)
        hh=[closed_G(3,n)-closed_G(3,n-1) for n in range(A+4)]
        T=fastconv(C,hh)
        assert T[:A]==f[:A]
        assert [T[A+j]-f[A+j] for j in range(4)]==jets
        ct['independent_ENTIRE_four_seed_jet_identifications']+=1
        if u>2*r:
            s0=(u-2*r)//3+1
            assert u<2*r+3*s0<=u+3
            if s==s0:
                ref,E=suffix_reference(V,W+3);N0=u+r+s+2
                assert N0>=W-1 and f[:N0]==ref[:N0]
                assert ref[N0]-f[N0]==(2 if a==1 else 1)
                ct['independent_analytic_first_crossing_ENTIRE_prefixes']+=1
        ct['independent_actual_all_count_hosts']+=1
        sha.update(str((a,u,r,s,f,jets)).encode())
    for case in range(16):
        r=57+case%3;s=1+case%4;u=[1,3,2*r+1,3*r+2][case%4];a=1+case%2
        U=[2]*u+[3]*r+[4]*s;V=[2]*(1+case%3)+[3]*57+[4]*(1+case%2);b=1
        if case%4==3:U=U+[6]
        M=7+case%3;X,Y=boxes(a,U),boxes(b,V);H,L,R=core(X,Y,M)
        host=[1]*a+U+[M]+list(reversed([1]*b+V));actual=greedy_ideal(host)
        assert H==actual and UI(actual)
        ct['independent_TRUE_greedy_ORIGINAL_arbitrary_binary_mixed_pairs']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        if case%4==3:ct['independent_legal_heavier_append_TRUE_ideals']+=1
        sha.update(str((host,actual)).encode())
    local=['mixed_binary_all_counts_actual_C_original_proof.tex','MixedBinaryAllCounts.lean','MixedBinaryAllCounts.log',
        'audit_mixed_binary_all_counts.py','audit_mixed_binary_all_counts.json','verify_mixed_binary_all_counts.py']
    deps=['mixed_binary_reference_ordinary_verification.json','mixed_binary_reference_direct_ordinary_proof.tex',
        'MixedBinaryReferenceOrdinary.lean','MixedBinaryReferenceOrdinary.log','verify_mixed_binary_reference_ordinary.py',
        'all_binary_ternary_complete_C_verification.json','all_binary_ternary_complete_C_proof.tex',
        'sharp_previous_ordinary_LC_verification.json','sharp_previous_ordinary_LC_proof.tex',
        'surplus_ordinary_tail_LC_proof.tex','certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
        'complete_three_four_verification.json','complete_three_four_actual_C_original_proof.tex',
        'StationaryFourCompleteC.lean','StationaryFourCompleteC.log','verify_binary_ternary_A2_original_family.py',
        'verify_universal_renewal_rounding.py','audit_joint_structure.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_mixed_binary_all_counts.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_ALL_BINARY_FOUR_COUNTS_FROM_FIFTY_SEVEN_THREES'
    out=dict(status='PASS_ACTUAL_ALL_BINARY_FOUR_COUNTS_FROM_FIFTY_SEVEN_THREES_AND_A10_ORIGINAL_FAMILY',new_scoped_reports=4,kernels=kernels(),
        actual_C='EVERYalpha>=1/r>=57/u>=0/s>=0 ACTUAL1alpha2u3r4s FULLC ALLcurrent/ALLshift. NOdensity/ratio cutoff. ALLbinary/three/fourcountsandpaddingUNBOUNDED.',
        sharp_ordinary='Forr>=57/u>=1 ENTIREordinaryFLCtailfromr+s+3 IFFu<=2r+3s. ALLu>2r+3s actualordinaryminoratW+1 EXACT-4^r5^s;NOTC/originalUIcounter.',
        true_seed='ALLfinitebinaryseedf retainsa,b,c,d=(H3-f)at3..6,BOUNDS1/2/5/11. ExactfirstFOURlossesa,wa+b,C(w+1,2)a+wb+c,(C(w+2,3)-r)a+C(w+1,2)b+wc+d. ALLw>=11budgetspayTHREEnewordinaryleftminors;WHOLElaterordinarytailLCconvolutioncoversALLlatermodes/zeros.',
        analytic_crossing='Ifu<=2r oldpure3ENTIREordinarytailseeds0. ForANYu>2r movingseed s0=floor((u-2r)/3)+1 has1<=h-u<=3,firstbinaryloss>=W-1,protectedreferenceheadthroughW-3/next-onlyimprovedW-2+OLDsharpactualordinarytailfromW-1joinALLranks. Whole4heredityALLs>=s0;smallercountsDENSEC. No unboundeddiagonalfinitepremise.',
        original_A10='A10=A9 UNIONALLactual1alpha2u3r4s(r>=57,ARBITRARYu/s). Finaldeletionclosed/C/kappa<=5=>FULLpairA2/ENTIREsourceconeBOTHnonrect/ORIGINALCOREandBOTHrelativesANYstrictcentralpeak+ONElegalheavierappend. NOamplification.',
        formal_scope='FOURnewcleanstandardaxiomSCOPEDreports:ALLrealfinitebinaryseedbudgets/completeanalyticfirstcrossing/WHOLEtwoNatcountinduction/exactprotectednegativecontroltripleguard. EarlierreferenceUNITbounds/genericstartups/LCconvolution/surplus/sharpactualordinary/root/C/originalmodelassemblyREUSEDorWRITTEN,NOTendtoendLeancompositions. NOnewfiniteproofpremise;allfinitehostsQAONLY.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',full_mixed_binary_three_four_C='OPEN_FOR_SMALL_THREE_COUNTS',new_finite_proof_premises=0,
        next='ReducefixedthreecountthresholdusingcompletefiniteROOT/minorbridgepredicates,thenremainingr1..smallthreshold andgeneralcapacities/beyondkappa5originalbridge. GeneralgoalNOTcomplete.',
        counts=dict(ct),primary_QA=primary['counts'],independent_state_sha256=sha.hexdigest(),seconds=time.monotonic()-start,
        local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'mixed_binary_all_counts_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
