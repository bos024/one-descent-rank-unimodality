"""Independent complete finite coverage, positive-box reconstruction, and Lean audit."""
from pathlib import Path
from math import comb
import hashlib,json,re,sys
from verify_subdegree_CI_entrance import suffix_boxes
from verify_divided_CI_surplus_three_primitive import kernel
from audit_arbitrary_Fibonacci_tail_late_C import sign,mul,power,sub
ROOT=Path(__file__).resolve().parent
NAMES=['golden_sharp_fifteenth_power','octuple_rank_two_first','octuple_rank_two_second','octuple_interior_and_rows',
       'octuple_quadratic_geometric_decay','double_subdegree_junction_scalar','double_subdegree_junction_gap',
       'perturbed_junction','negative_initial_atom_is_absent','long_three_endpoint_minor',
       'long_four_endpoint_minor','first_primitive_minor','actual_ordinary_seed_losses']

def multiplicities(cap,degree):
    if cap==2:
        if degree%2==0:yield [3]*(degree//2)
        return
    for copies in range(degree//cap+1):
        for rest in multiplicities(cap-1,degree-copies*cap):
            yield rest+[cap+1]*copies

def main():
    qa=json.loads((ROOT/'audit_double_subdegree_CI_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_DOUBLE_SUBDEGREE_UNDER_PROOF_AUDIT'
    assert qa['state_sha256']=='f94e0f5c116985184632bd8587659f08f52b05ade8b54a15aec6f742d8da0d66'
    produced={(x['u'],tuple(x['V'])):x for x in qa['complete_small_degree_profiles']}
    keys=set();integers=set();hosts=minor_count=0;sha=hashlib.sha256()
    for u in (14,15):
        for V in multiplicities(u+2,u+2):
            if len(V)<2:continue
            key=(u,tuple(V));assert key not in keys;keys.add(key);row=produced[key]
            assert len(row['hosts'])==u+2
            for alpha,host in enumerate(row['hosts'],1):
                F=suffix_boxes(alpha,[2]*u+V);W=sum(V)
                g=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=g.index(max(g));margins=[]
                for n in range(1,M):
                    z=g[n]**2-g[n-1]*g[n+1];assert z>=0;integers.add(z);margins.append(z);minor_count+=1
                assert alpha==host['alpha'] and M==host['first_tail_mode'] and margins==host['margins']
                # Independent full positive F, not the producer's signed CI source formula.
                sha.update(json.dumps([u,V,alpha,F],separators=(',',':')).encode());hosts+=1
    assert keys==set(produced) and len(keys)==119 and hosts==1969 and minor_count==21127
    assert sorted(integers)==qa['integer_margins'] and len(integers)==11087
    source=(ROOT/'DoubleSubdegreeCertificate.lean').read_text(encoding='utf8')
    chunks=re.findall(r'def part\d+ : List ℤ := \[([^]]*)\]',source)
    rows=[int(x) for chunk in chunks for x in chunk.split(', ')]
    assert len(chunks)==29 and rows==sorted(integers)
    bridge_profiles=bridge_hosts=0
    for u in range(2,16):
        for V in multiplicities(u+2,u+2):
            if len(V)<2:continue
            W=sum(V);w=u+len(V)
            # A sufficiently long actual binary prefix realizes the reference
            # through ALL reads. Both sides use only positive suffix boxes.
            R=suffix_boxes(1,[2]*(W+3)+V);x=R[W]-R[W-1];y=R[W+1]-R[W]
            A=x*x+x*y-y*y;assert y>=x>0 and A>0
            for alpha in (1,2,3,u+2):
                F=suffix_boxes(alpha,[2]*u+V)
                d0,d1=(2,2*w+1) if alpha==1 else (1,w+2) if alpha==2 else (1,w+1)
                assert F[:W]==R[:W] and F[W]==R[W]-d0
                assert F[W+1]-F[W]==y-d1
                seed=F[W]*(F[W]-F[W-1])-F[W-1]*(F[W+1]-F[W])
                assert seed==A-2*d0*x+(d1-d0)*y+d0*d0>0;bridge_hosts+=1
            bridge_profiles+=1
    # The sole sharpened geometric base is an exact Q(phi) inequality.
    q=(-1,1);base=sub((1,0),mul((1360,0),power(q,15)))
    assert base==(1342321,-829600) and sign(base)>0
    # Polynomial identities have degrees three/four; verify distinct evaluations,
    # independently of the producer's polynomial multiplication routine.
    for item in qa['head_polynomial_coefficients']:
        k=item['k'];coeff=[tuple(x) for x in item['coefficients_u_minus_16']]
        for u in range(16,22):
            Q0=(1,0);Q1=sub((u,0),q);Q2=sub((comb(u,2),0),mul(q,Q1));Q3=sub((comb(u,3),0),mul(q,Q2))
            K=sub(mul(Q2,Q1),Q3) if k==1 else sub(mul(Q2,Q2),mul(Q3,Q1))
            T=tuple(a+b+c for a,b,c in zip(Q2 if k==1 else Q3,mul(mul((2,0),q),Q1 if k==1 else Q2),mul(mul(q,q),Q0 if k==1 else Q1)))
            lhs=mul((12,0),sub(K,mul(mul((8,0),mul(q,q)),T)))
            rhs=(sum(a*(u-16)**i for i,(a,b) in enumerate(coeff)),sum(b*(u-16)**i for i,(a,b) in enumerate(coeff)))
            assert lhs==rhs and all(sign(c)>0 for c in coeff)
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_COMPLETE_DOUBLE_SUBDEGREE_RECONSTRUCTION',profiles=119,hosts=hosts,comparisons=minor_count,distinct_integer_margins=len(integers),bridge_profiles=bridge_profiles,bridge_hosts=bridge_hosts,independent_state_sha256=sha.hexdigest())),flush=True);return
    kernels={'DoubleSubdegreeCI':kernel('DoubleSubdegreeCI',NAMES),
             'DoubleSubdegreeCertificate':kernel('DoubleSubdegreeCertificate',['all_integer_margins'])}
    files=['double_subdegree_CI_entrance_proof.tex','DoubleSubdegreeCI.lean','DoubleSubdegreeCI.log',
        'DoubleSubdegreeCertificate.lean','DoubleSubdegreeCertificate.log','audit_double_subdegree_CI_entrance.py',
        'audit_double_subdegree_CI_entrance.json','emit_double_subdegree_certificate.py','verify_double_subdegree_CI_entrance.py',
        'mode_only_uniform_tail_closure_verification.json','degree_boundary_CI_entrance_verification.json',
        'all_padding_CI_entrance_verification.json','finite_initial_ones_relative_derivative.tex',
        'homogeneous_reference_complete_C.tex']
    assert all((ROOT/f).exists() for f in files)
    out=dict(status='PASS_UNBOUNDED_DOUBLE_SUBDEGREE_ALL_PADDING_DERIVATIVE_ENTRANCE_AND_LATE_C',new_scoped_reports=14,kernels=kernels,
        theorem='ALL sorted nonempty CI tails V>=3, degreeh=sum(t-1), EVERYbinaryu>=h-2, EVERYpaddingalpha>=1: ALLactualCshiftsR>=3 atEVERYcurrentN>=W+1,W=sumV. Newmultifactorboundaryu=h-2;oldthresholdu>=h-1andonefactortheoremreused. GeneralearlierC/A2/originalUIOPEN.',
        auxiliary='Foru>=16,h=u+2,r>=2,thedividedquotientJmayhaveNEGATIVEconstant. Itsrank-onepositiveTAILisglobalLC,andENTIREpositiveprimitiveisglobalLC. EightfoldrobustheadforANYnonnegativeLCN0=1,N1<=u/2+1hasNODEGREEbound. Long[3][u+1]and[4][u]endpointsareexplicit. Negativeprimitiveat0vanishesinALLcuttriplesfroma+2;truecsourceatomretained. ActualsignedtailfromWincludesextraunit.',
        actual_C_entrance='BOTHlossesretained:firstfinitebinaryDlossatz^W E/(1-z-z2),separatefiniteonesatz^(W+alpha-1)E. Firsttwolosses(2,2w+1)/(1,w+2)/(1,w+1);ordinaryFseedstrictlypositiveandDentryratio<phi. ALLcumulativeprefixesbeforeWareunchangedreference>phi. DerivativeLCandtwointegrationsproveALLlateCreads.',
        small_cases='u<=13usesregisteredALLsmallbinarylateDLC;ONLYu14/15needNEW119COMPLETEdegreeprofiles/1969paddinghosts/21127minorcomparisons/11087distinctintegerkernelmargins. Noenumerationofgeneraluasserted.',
        hereditary='Actual late pre-mode D-LC now propagates from ANY submultiset of degree u+2, as well as old u+1/long-factor seeds. Hence ALL u>=0,ALL r with2r>u,ALLalpha have lateDLCfor1alpha2^u3^r atALLcentresN>=3r+1. Any remaining deletion-minimal crossing seed has EVERYdegree3<=di<=u (NOcapacity3),u+3<=h<=2u,h-min di<=u,and may have NOsubsetofdegreeu+1/u+2. DerivativeLCONLY;C/earlyF/GareNOTinsertioninvariant.',
        formal_scope='THIRTEENnewscopedunboundedscalar/kernelreportsplusONEcompleteintegercertificate(propextonly). Wholequotient/ULCconvolution/window/sign/source/CintegrationassemblyisWRITTEN,notend-to-endLeanactualcompositions. Sharpenedq15baseisBOTHdirectlykernelprovedandindependentlyexactfieldchecked.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_late_C_threshold='u>=h-2',
        independent_profiles=119,independent_hosts=hosts,independent_comparisons=minor_count,distinct_integer_margins=len(integers),
        independent_bridge_profiles=bridge_profiles,independent_bridge_hosts=bridge_hosts,
        independent_state_sha256=sha.hexdigest(),state_sha256=qa['state_sha256'],QA=qa['counts'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'double_subdegree_CI_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
