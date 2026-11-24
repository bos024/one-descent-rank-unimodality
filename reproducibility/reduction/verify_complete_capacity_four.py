"""Independent COMPLETE finite-boundary proof reconstruction and separate QA.
No sampled nonfailure is used as a universal premise.
"""
from pathlib import Path
from collections import Counter,defaultdict
from random import Random
import sys,json,re,time,hashlib
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from verify_mixed_binary_reference_ordinary import suffix_reference
from verify_mixed_three_four_proper_quotient import ci
from verify_binary_ternary_A2_original_family import boxes,core,greedy_ideal,UI
from verify_universal_renewal_rounding import closed_G
from audit_joint_structure import fastconv

def at(a,n):return a[n] if 0<=n<len(a) else 0
def reports(name,count):
    src=(ROOT/(name+'.lean')).read_text(encoding='utf8');log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert 'native_decide' not in src and not any(s in log for s in ['warning:','error:','sorryAx','ofReduceBool','failed'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S);assert len(rows)==count
    out={}
    for n,v in rows:
        a=[s.strip() for s in v.split(',') if s.strip()]
        assert set(a)<={'propext','Classical.choice','Quot.sound'};out[n]=a
    return out
def main():
    st=time.monotonic();ct=Counter();positions=defaultdict(int);sha=hashlib.sha256();integers=set()
    data=json.loads((ROOT/'complete_capacity_four_base_data.json').read_text(encoding='utf8'))
    def T(s):
        C=[0]*(4*s+1);C[0]=1
        for j in range(s):
            for i,v in enumerate(ci(0,j)):C[4+j+i]+=v
        hh=[closed_G(3,n)-closed_G(3,n-1) for n in range(105)]
        return fastconv(C,hh)[:105]
    Ts={s:T(s) for s in range(1,18)}
    def record(kind,state,margins):
        assert min(margins,default=0)>=0,(kind,state,min(margins))
        j=positions[kind];assert data['contexts'][kind][j]==state,(kind,j)
        positions[kind]+=1;integers.update(margins)
        ct[kind+'_contexts']+=1;ct[kind+'_margins']+=len(margins)
        sha.update(json.dumps([kind,state,margins],separators=(',',':')).encode())
    for r in range(1,57):
        for s in range(1,18):
            if r+s<11:continue
            A=r+s+3;v=Ts[s]
            record('small_unit_reference',dict(r=r,s=s,read=v[A-1:A+4]),
                [v[n]**2-v[n-1]*v[n+1]+v[n-1] for n in range(A,A+3)])
    for s in range(1,18):
        r=3*s-3
        if r<1:continue
        n=r+s+2;v=Ts[s]
        record('first_boundary_unit',dict(r=r,s=s,n=n,read=v[n-1:n+2]),[v[n]**2-v[n-1]*v[n+1]+v[n-1]])
    hh=[closed_G(3,n)-closed_G(3,n-1) for n in range(7)]
    rows=[];representatives={}
    for u in range(1,8):
        for alpha in range(1,8):
            f=boxes(alpha,[2]*u);jets=[hh[n]-at(f,n) for n in range(3,7)]
            rows.append(dict(u=u,alpha=alpha,coefficients=[at(f,n) for n in range(7)],jets=jets))
            representatives.setdefault(tuple(jets),(alpha,u))
    assert rows==data['binary_seed_clamp']
    jets=sorted(representatives);assert [list(v) for v in jets]==data['distinct_seed_jets']
    for r in range(1,10):
        for s in range(1,11-r):
            if (r,s)==(1,1):continue
            A=r+s+3
            for a,b,c,d in jets:
                alpha,u=representatives[(a,b,c,d)]
                f=boxes(alpha,[2]*u+[3]*r+[4]*s)
                F=[at(f,n) for n in range(A-1,A+4)]
                record('small_full_seed_startup',dict(r=r,s=s,jets=[a,b,c,d],actual_reads=F),
                    [F[j]**2-F[j-1]*F[j+1] for j in range(1,4)])
    for r in range(1,8):
        for s in range(1,9-r):
            if (r,s)==(1,1):continue
            W=3*r+4*s;f,E=suffix_reference([3]*r+[4]*s,W+3)
            record('small_four_terminal',dict(r=r,s=s,read=f[W-4:W+2]),
                [f[n]**2-f[n-1]*f[n+1] for n in range(W-3,W+1)])
    for r,s in [(r,0) for r in range(2,6)]+[(1,2)]:
        W=3*r+4*s;A=r+s+3;f,E=suffix_reference([3]*r+[4]*s,W+3)
        record('small_reference_ordinary_base',dict(r=r,s=s,prefix=f[:W+2]),
            [f[n]**2-f[n-1]*f[n+1] for n in range(A,W+1)])
    for r,s,us in [(r,0,range(1,2*r+1)) for r in range(2,6)]+[(1,2,range(1,9))]:
        for u in us:
            w=u+r+s;L=(3*u+4*r+5*s)//2;alpha0=L-w+1;A=r+s+3
            largest=boxes(alpha0,[2]*u+[3]*r+[4]*s)
            for alpha in range(1,alpha0+1):
                f=boxes(alpha,[2]*u+[3]*r+[4]*s)
                D=[0,0]+[max(0,f[n]-f[n-1]) for n in range(2,len(f))]
                assert D.index(max(D))<=L
                record('complete_actual_ordinary_base',dict(r=r,s=s,u=u,alpha=alpha,alpha0=alpha0,L=L,A=A,prefix=f[:L+1]),
                    [f[n]**2-f[n-1]*f[n+1] for n in range(A,L)])
            for alpha in [alpha0+1,alpha0+9]:
                f=boxes(alpha,[2]*u+[3]*r+[4]*s)
                assert f[:L+1]==largest[:L+1]
    for kind,items in data['contexts'].items():assert positions[kind]==len(items),kind
    assert dict(ct)==data['counts'] and sha.hexdigest()==data['state_sha256']
    values=sorted(integers);assert values==data['integer_margins'] and len(values)==3059
    src=(ROOT/'CompleteCapacityFourBase.lean').read_text(encoding='utf8')
    chunks=re.findall(r'private theorem (chunk_\d+) : \((.*?)\) = true := by decide',src,re.S)
    assert len(chunks)==22
    flat=[];exprs=[]
    for j,(name,expr) in enumerate(chunks):
        assert name=='chunk_'+str(j)
        vv=[int(x) for x in re.findall(r'decide \(\(0 : Int\) ≤ (\d+)\)',expr)]
        assert vv==values[140*j:140*(j+1)]
        expected=' && '.join(f'decide ((0 : Int) ≤ {v})' for v in vv)
        assert expr==expected;flat.extend(vv);exprs.append('('+expr+')')
    assert flat==values
    public='theorem complete_all_integer_bases : ('+' && '.join(exprs)+') = true := by\n  simp only ['+', '.join(name for name,expr in chunks)+', Bool.and_self]'
    assert public in src
    kernels={'CompleteCapacityFour':reports('CompleteCapacityFour',6),'CompleteCapacityFourBase':reports('CompleteCapacityFourBase',1)}
    finite_ct=dict(ct)
    # Everything below is SEPARATE QA and is not in the finite proof digest.
    rng=Random(170493)
    for case in range(96):
        alpha,beta=rng.randint(1,5),rng.randint(1,5)
        u,r,s=rng.randint(0,20),rng.randint(0,12),rng.randint(0,12)
        uu,rr,ss=rng.randint(0,20),rng.randint(0,12),rng.randint(0,12)
        U=[2]*u+[3]*r+[4]*s;V=[2]*uu+[3]*rr+[4]*ss
        if case%12==0:
            # One legal heavier append with weight balance explicitly retained.
            if alpha+sum(U)<beta+sum(V):alpha,beta,U,V=beta,alpha,V,U
            U=U+[6]
        M=7+case%5;X,Y=boxes(alpha,U),boxes(beta,V);H,L,R=core(X,Y,M)
        host=[1]*alpha+U+[M]+list(reversed([1]*beta+V));actual=greedy_ideal(host)
        assert actual==H and UI(actual)
        ct['independent_TRUE_greedy_ORIGINAL_complete_alphabet']+=1
        ct['independent_TRUE_greedy_ORIGINAL_rank_counts']+=len(actual)
        if case%12==0:ct['independent_legal_heavier_append_ORIGINAL_ideals']+=1
    local=['complete_capacity_four_C_original_proof.tex','CompleteCapacityFour.lean','CompleteCapacityFour.log',
        'CompleteCapacityFourBase.lean','CompleteCapacityFourBase.log','build_complete_capacity_four_bases.py',
        'complete_capacity_four_base_data.json','audit_complete_capacity_four.py','audit_complete_capacity_four.json','verify_complete_capacity_four.py']
    deps=['mixed_binary_all_counts_verification.json','mixed_binary_all_counts_actual_C_original_proof.tex','MixedBinaryAllCounts.lean','MixedBinaryAllCounts.log',
        'mixed_binary_reference_ordinary_verification.json','mixed_binary_reference_direct_ordinary_proof.tex','MixedBinaryReferenceOrdinary.lean','MixedBinaryReferenceOrdinary.log',
        'all_binary_ternary_complete_C_verification.json','all_binary_ternary_complete_C_proof.tex','stationary_four_complete_C_verification.json','stationary_four_complete_C_proof.tex',
        'complete_three_four_verification.json','complete_three_four_actual_C_original_proof.tex',
        'two_nonbinary_complete_C_verification.json','two_nonbinary_complete_C_proof.tex',
        'sharp_previous_ordinary_LC_verification.json','sharp_previous_ordinary_LC_proof.tex',
        'previous_boundary_C_verification.json','previous_boundary_C_proof.tex','universal_physical_boundary_C_verification.json','universal_physical_boundary_C_proof.tex',
        'sharpened_forward_derivative_centers.tex','SharpenedForwardDerivativeCenters.lean','SharpenedForwardDerivativeCenters.log',
        'certified_kappa_five_original_family_verification.json','certified_kappa_five_original_family_refinement.tex',
        'ThreeFourAllFourCounts.lean','ThreeFourAllFourCounts.log','MixedThreeFourActualCut.lean','MixedThreeFourActualCut.log',
        'TribonacciInverseClosure.lean','TribonacciInverseClosure.log','TribonacciInverseCompleteCertificate.lean','TribonacciInverseCompleteCertificate.log',
        'verify_mixed_binary_reference_ordinary.py','verify_mixed_three_four_proper_quotient.py',
        'verify_binary_ternary_A2_original_family.py','verify_universal_renewal_rounding.py','audit_joint_structure.py']
    for name in [n for n in deps if n.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,digest in dep['sha256'].items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==digest,(name,n)
    primary=json.loads((ROOT/'audit_complete_capacity_four.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_EXACT_QA_COMPLETE_CAPACITY_FOUR_C_AND_ORIGINAL_FAMILY'
    out=dict(status='PASS_COMPLETE_ALL_COUNTS_CAPACITY_FOUR_ACTUAL_C_AND_A11_ORIGINAL_UNAMPLIFIED_FAMILY',new_scoped_reports=7,kernels=kernels,
        actual_C='EVERYalpha>=1/u>=0/r>=0/s>=0 ACTUAL1alpha2u3r4s FULLC ALLcurrent/ALLshift. ENTIREcapacity<=4armalphabet. NOcount/ratio/density/paddingcutoff.',
        reference='EVERYr/s mixedinfiniteBINARYreferenceFULLC ALLcurrents/shifts. Ordinaryheadr+s+3..W forr>=2or(r1/s>=2);EXCEPTIONr1s1ordinaryminor-7at5retainedandpaidbyOLDtwo-nonbinaryC.',
        finite_inputs='COMPLETE907unitcontexts2721margins+16firstboundaryunits+49binaryseedclamprows/15distinctjets/660fullstartupcontexts1980margins+27fourterminalcontexts108minors+FIVEreferencebases26minors+246actualbasehosts2048ordinaryminorsALLpadding/rankclamped. EXACT3059distinctintegerobligations22chunksONEkernelaggregate,independentEVERYcontext/read/partition/statehash/chunk/publicaggregateMATCH.',
        full_count_reduction='Forr>=2 actualu<=2r ordinarybaseats0 (smallr2..5FULLfiniteclamp,largerOLD). ForANYu>2r ANALYTICfirstcrossingseed andwhole4heredity;smallerh<=uDENSEC. Distinguishedr1 actualu<=8baseFIXEDs2;u>8 firstcrosss0>=3;lowercounts0/1OLDcompleteC. u0/r0OLDALLcountfamilies. Completeunboundedcasepartitionkernelchecked.',
        root_and_startup='NewALLm>=9/3s<m cubicentry2*2^s*b^floor<1 andSEVENsmallrootentries,oldlambda>=1839/1000. UnitminorFAILS7smallreads,soALLw<=10ACTUALseedjetstartupscheckedDIRECTLY,EXCEPtr1s1handledOLDtwojumpC. No discardedsourceorwrongtailread.',
        original_A11='A11=A10 UNIONALLactualarmswithnononecapacities<=4. Finaldeletionclosed/FULLC/kappa<=5=>FULLpairA2/ENTIREpositive-sourceconeBOTHnonrect/ORIGINALstrictCOREandBOTHrelativesANYstrictcentralpeak+ONEarbitrarylegalheavierappend. NOamplification. Wholearmalphabet<=4,allTHREEcountsUNRESTRICTED.',
        formal_scope='SEVENnewreports:SIXcleanstandardaxiomSCOPEDanalyticroot/completeparameterandpadding/base-selectionkernels+ONEordinaryBoolkernelaggregateALL3059finiteintegerproofpremises(22chunks). Actualmodel/LCconvolution/oldC/root/originalassemblyWRITTEN,notendtoendLeancompositions. NEWfinitepremisesEXPLICITCOMPLETEandindependentlyreconstructed;largerQAseparate.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',full_mixed_binary_three_four_C='PROVED_ALL_COUNTS',
        next='Generalcapacities>=5 andoriginalbridgebeyondfirstmissingfive. Applydirectordinary/window/sourcepackagetoadjacenthighercapacityblockswithoutassumingunprovedCDF-to-coefficientimplications. GeneralgoalNOTcomplete.',
        finite_proof_counts=finite_ct,finite_state_sha256=sha.hexdigest(),independent_counts=dict(ct),primary_QA=primary['counts'],seconds=time.monotonic()-st,
        local_files=local,dependency_files=deps,sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps})
    (ROOT/'complete_capacity_four_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
