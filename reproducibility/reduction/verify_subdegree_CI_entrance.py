"""Independent full bounded-exception reconstruction, separate from random QA."""
from pathlib import Path
from itertools import combinations_with_replacement
import json,hashlib,re,sys
from verify_divided_CI_surplus_three_primitive import kernel
from verify_degree_boundary_CI_entrance import reverse_divided
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign
from audit_binary_CI_infinite_padding_entrance import minor
ROOT=Path(__file__).resolve().parent
ZERO=(0,0);Q=(-1,1)

def suffix_boxes(alpha,U):
    N=alpha+sum(U);P=[1];F=[0]*(N+1)
    for t in reversed(U):
        for n,v in enumerate(P):F[n]+=v
        P=fastconv(P,[0]+[1]*t)
    full=fastconv(P,[1]*(alpha+1))
    for n,v in enumerate(full):F[n]+=v
    return F+[0]*5

def main():
    qa=json.loads((ROOT/'audit_subdegree_CI_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_PASS_SUBDEGREE_CI_REFINEMENT_UNDER_PROOF_AUDIT'
    assert qa['state_sha256']=='60362ddf4a7d08dc14025a3bf2dab9cc89dd65fbee089fd3e1d6bdc9cc603186'
    produced={(z['u'],tuple(z['V'])):z for z in qa['complete_small_contexts']}
    starts={(z['u'],tuple(z['V']),z['alpha']):z for z in qa['complete_small_startup_contexts']}
    keys=set();cert=set();startup_keys=set();integers=set();comparisons=0
    for length in range(2,9):
        for V in combinations_with_replacement(range(3,18),length):
            u=sum(t-1 for t in V)-1
            if not 3<=u<=15:continue
            key=(u,V);keys.add(key);assert key in produced
            L=[1]
            for t in V:L=fastconv(L,[1]*t)
            J=reverse_divided(L,u);assert all(sign(x)>0 for x in J);cert.update(J)
            for n in range(2,len(J)-1):cert.add(minor(J,n))
            d=[sub(x,J[n-1] if n else ZERO) for n,x in enumerate(J)]
            dp=[x if sign(x)>0 else ZERO for x in d]
            for n in range(2,len(dp)-1):cert.add(minor(dp,n))
            budget=sub(mul(Q,J[1]),J[0]);assert sign(budget)>0;cert.add(budget)
            if u+length>=8:continue
            for alpha in range(1,u+1):
                sk=(u,V,alpha);startup_keys.add(sk);row=starts[sk]
                # Independent positive suffix-box sum, NOT iterated append or quotient/source subtraction.
                F=suffix_boxes(alpha,[2]*u+list(V))
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))];ell=D.index(max(D));margins=[]
                for n in range(sum(V)+1,ell):
                    M=D[n]**2-D[n-1]*D[n+1];assert M>=0
                    margins.append(M);integers.add(M);comparisons+=1
                assert ell==row['first_mode'] and margins==row['margins']
    assert keys==set(produced) and len(keys)==215
    assert sorted(cert)==[tuple(x) for x in qa['complete_small_scalar_margins']] and len(cert)==11853
    assert all(sign(x)>=0 for x in cert)
    L=fastconv([1]*3,[1]*3);control=reverse_divided(L,3)
    assert minor(control,1)==(62,-41) and sign(minor(control,1))<0
    assert qa['actual_multifactor_first_ordinary_minor_control']['margin']==[62,-41]
    assert startup_keys==set(starts) and len(startup_keys)==17 and comparisons==31
    assert sorted(integers)==qa['complete_small_startup_integer_margins'] and len(integers)==24
    name='SubdegreeCIChunkCertificate';source=(ROOT/(name+'.lean')).read_text(encoding='utf8')
    lean_rows=[tuple(map(int,x)) for x in re.findall(r'^  \((-?\d+), (-?\d+)\)',source,re.M)]
    assert lean_rows==sorted(cert)
    match=re.search(r'def actualStartupMargins : List ℤ := \[([^]]*)\]',source)
    assert match and list(map(int,match.group(1).split(', ')))==sorted(integers)
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_COMPLETE_RECONSTRUCTION_ONLY',quotient_contexts=215,field_margins=11853,actual_startups=17,actual_minors=comparisons,integer_margins=24)),flush=True);return
    names=['relaxed_fourfold_row_zero','inverse_initial_minor_identity','inverse_initial_minor_payment',
        'inverse_strict_initial_budget','subdegree_junction_scalar','subdegree_interval_junction_gap',
        'golden_seventh_power_bound','subdegree_uniform_atom_payment','exceptional_endpoint_negative',
        'actual_boundary_unit_alignment','subdegree_positive_Cassini_seed']
    kernels={'SubdegreeCI':kernel('SubdegreeCI',names),name:kernel(name,['golden_fine_interval','all_scalar_margins'])}
    log=(ROOT/(name+'.log')).read_text(encoding='utf8')
    assert "'"+name+".complete_actual_startup_margins' does not depend on any axioms" in log
    assert log.count('does not depend on any axioms')==1;kernels[name]['complete_actual_startup_margins']=[]
    files=['subdegree_CI_entrance_proof.tex','SubdegreeCI.lean','SubdegreeCI.log',name+'.lean',name+'.log',
        'audit_subdegree_CI_entrance.py','audit_subdegree_CI_entrance.json','emit_subdegree_CI_certificate.py',
        'verify_subdegree_CI_entrance.py','degree_boundary_read_correction.tex',
        'degree_boundary_CI_entrance_verification.json','degree_boundary_CI_entrance_proof.tex',
        'all_padding_CI_entrance_verification.json','all_padding_CI_entrance_theorem.tex',
        'golden_signed_primitive_cut_closure.tex','divided_CI_later_primitive_proof.tex',
        'infinite_padding_full_deficit_LC.tex','binary_CI_infinite_padding_entrance.tex',
        'lc_positive_primitive_window_closure.tex','homogeneous_reference_complete_C.tex','general_one_jump_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_SUBDEGREE_MULTITAIL_ENTRANCE_AND_ALL_LATE_C',new_scoped_reports=14,kernels=kernels,
        quotient='For EVERY CI L with AT LEAST TWO factors[t],t>=3, degree h, at EXACT u=h-1: J=((1+z)^uL-psi^u L(-phi))/(1+qz) is positive UNIMODAL; deleting rank0 makes its ordinary coefficients globally LC; qJ1>J0; its positive primitive is LC at EVERY centre>=2. Ordinary LC at first centre is NOT asserted. ONE-FACTOR version is FALSE and is NOT used. Uniform u>=16 proof uses LARGEST-interval induction, registered surplus old quotient, relaxed FOURFOLD no-degree-bound head, enlarged junction range2r<=u-1, perturbed gap u/40 and ONE exact long endpoint. COMPLETE215 low-u contexts independently reverse-divided,11853 scalar margins.',
        inverse_and_cut='Generic finite positive b need only be UNIMODAL, with its positive primitive LC after deleting rank0, for the signed-primitive finite-cut theorem; full ordinary LC of b is unnecessary. Separately if b after deleting rank0 is global LC and qb1>=b0, its right-geometric inverse x is GLOBAL LC including centre0, by the exact first minor x0(qb1-b0)+qb0b1 and ordinary tail convolution. Both written assemblies reuse existing constant-cut/window kernels, with two NEW exact/positive first-inverse-minor kernels.',
        actual_boundary='At u=h-1,r>=2 the ACTUAL derivative from physical W is EXACTLY the geometric quotient-cut model: its extra numerator unit gives x_(-1)=C_(u-1)+1, ALL later x_s=C_(u+s). Thus actual LC holds at ALL pre-first-mode centres W+1<=N<ell for EVERY padding. First/second source startup payments at w>=8 plus COMPLETE17 actual small-w paddings/31 minors/24 integer margins cover ALL padding, with analytic alpha>=u+1 clamp. No false identification of a previous actual read with a formal coefficient lacking its extra unit.',
        actual='EVERY ACTUAL sorted nonempty V>=3, h=sum(t-1),W=sumV, EVERY binary count u>=h-1 and EVERY padding alpha>=1 satisfies EVERY C shift R>=3 at EVERY N>=W+1. NEW u=h-1,r>=2 first defect is W+1; its entrance ratio is STRICTLY below phi because conjugate error c<0. Unchanged reference cumulative reads through W exceed phi. Correct ordinary seed F_(W-1)=a,F_W=a+b has margin A_V+delta*a>0. Actual LC then finite F/G integration pays every later read. ALL one-factor tails use established complete one-jump C; u>=h uses registered degree-boundary theorem.',
        finite_reduction='For EACH fixed V, shorter binary-count complement is now only 0<=u<h-1, rather than u<h. Earlier reference C at N<=W is still OPEN. General C/A2/original UI OPEN; first unresolved general-C count6 and original least-counterexample numerical bounds unchanged.',
        correction='degree_boundary_read_correction.tex withdraws an UNUSED aside in the immutable degree-boundary proof claiming the ordinary seed at W can fail. Exact reference identity F_j=r_(j+2)-B_(j+2) gives F_(W-1)=r_(W+1), no added unit. Previous theorem proof uses valid F_W/F_(W+1) reads and is unaffected. NEW subdegree seed uses the corrected earlier read and has independent literal coefficient reconstruction.',
        formal_scope='FOURTEEN NEW reports: ELEVEN SubdegreeCI scalar/relaxed-row-zero/inverse/junction/power/endpoint/alignment/Cassini-seed kernels and THREE SubdegreeCIChunkCertificate fine-root/ALL11853-field/ALL24-integer certificates, last AXIOM FREE. Ordinary Lean reduction over31 chunks; no native axiom. Independent capacity-multiset grammar/reverse polynomial division covers all215 low-u quotients; independent positive SUFFIX-BOX sums cover all17 actual startup hosts, not the iterated append used by QA. ULC/window/LC convolution, UNIMODAL-b cut assembly, actual source identification, mode/padding/all-read integration are written proofs, not end-to-end Lean of all compositions. Old kernels reused without recounting.',
        remaining='0<=u<h-1; earlier arbitrary-tail reference C N<=W; general C/A2; original deep/mixed/incoming branches; ORIGINAL general unamplified one-descent UI OPEN. NO original numerical least-counterexample improvement.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',independent_small_contexts=215,
        independent_actual_startups=17,independent_actual_startup_minors=31,field_margins=11853,integer_margins=24,
        QA=qa['counts'],state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'subdegree_CI_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
