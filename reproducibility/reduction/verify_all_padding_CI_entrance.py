"""Register the repaired primitive, geometric cut, and ALL-padding CI entrance."""
from pathlib import Path
from itertools import combinations_with_replacement
from math import comb
import json,re,hashlib
from verify_divided_CI_surplus_three_primitive import kernel
from audit_joint_structure import fastconv
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign,evaluate
from audit_binary_CI_infinite_padding_entrance import minor
from audit_minimum_staircase_scaled_dyadic import arm_prefix
from audit_padding_three_local_prefix import parts
ROOT=Path(__file__).resolve().parent
ZERO=(0,0);PHI=(0,1)

def reverse_divided(L,u):
    E=fastconv(L,[comb(u,j) for j in range(u+1)]);J=[ZERO]*(len(E)-1);following=ZERO
    for n in range(len(E)-1,0,-1):
        J[n-1]=mul(PHI,sub((E[n],0),following));following=J[n-1]
    assert J[0]==sub((E[0],0),evaluate(E,(0,-1)))
    return J

def main():
    kernels={}
    kernels['DividedCILaterPrimitive']=kernel('DividedCILaterPrimitive',[
        'weighted_power_decay','double_quadratic_kernel_payment','double_last_head_payment',
        'double_row_zero_payments','nonempty_junction_scalar','nonempty_interval_junction_gap',
        'empty_interval_junction_gap'])
    kernels['GoldenPrimitiveCut']=kernel('GoldenPrimitiveCut',[
        'constant_cut_preserves_LC','signed_primitive_cut_identity',
        'first_source_minor_payment','second_source_minor_payment'])
    kernels['DividedCILaterSmallCertificate']=kernel('DividedCILaterSmallCertificate',[
        'golden_fine_interval','all_scalar_margins'])
    slog=(ROOT/'DividedCILaterSmallCertificate.log').read_text(encoding='utf8')
    assert "'DividedCILaterSmallCertificate.complete_actual_startup_margins' does not depend on any axioms" in slog
    assert slog.count('does not depend on any axioms')==1
    kernels['DividedCILaterSmallCertificate']['complete_actual_startup_margins']=[]
    qa=json.loads((ROOT/'audit_divided_CI_later_primitive.json').read_text(encoding='utf8'))
    cut=json.loads((ROOT/'audit_all_padding_primitive_cut.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_REPAIRED_ALL_DEGREE_LATER_DIVIDED_CI_PRIMITIVE'
    assert cut['status']=='PASS_EXACT_QA_SIGNED_PRIMITIVE_CUT_AND_ALL_PADDING_ACTUAL_LATE_C'
    expected=dict(complete_small_later_primitive_minors=1653,exact_double_robust_row_zero_payments=2967,
        exact_double_robust_kernel_rows=81926,exact_two_exceptional_single_interval_boundary_formulas=138,
        exact_generic_double_robust_head_minors=14961,generic_LC_double_budget_contexts=500,
        exact_double_perturbed_X_head_minors=109708,exact_repaired_low_head_identity_contexts=1600,
        exact_nonempty_old_tail_strong_junction_payments=1426,exact_later_only_primitive_window_minors=194158,
        exact_entire_CI_later_primitive_minors=218461,repaired_CI_induction_contexts=1600,
        exact_empty_old_tail_strong_junction_payments=131)
    cutexpected=dict(complete_small_actual_pre_mode_LC_minors=135,
        exact_right_geometric_actual_Cinf_identifications=169730,
        exact_signed_primitive_convolution_and_constant_cut_identities=41813,
        exact_generic_cut_LC_after_deleted_initial_primitive=39606,
        exact_actual_all_padding_through_first_mode_LC_minors=80157,
        exact_uniform_first_source_startup_minors=2366,
        exact_all_padding_all_read_prefix_minimum_C_payments=216092,actual_all_padding_CI_contexts=1200)
    assert qa['counts']==expected and cut['counts']==cutexpected
    assert qa['state_sha256']=='e8ce8134e686e2b430a206529286ab234a88d23623bc707fd7b57e5232030cf0'
    assert cut['state_sha256']=='2c50f9993f124f4cb5a92d7bcb6ea1d76ac7f6903d49f404f0baf575d99081cb'
    # Independent COMPLETE capacity grammar and REVERSE polynomial division.
    produced={(row['u'],tuple(row['degree_partition'])):row for row in qa['small_contexts']}
    independent=set();cert=set()
    for u in range(1,12):
        for length in range(6):
            for V in combinations_with_replacement(range(3,12),length):
                if sum(t-1 for t in V)>u-1:continue
                key=(u,tuple(t-1 for t in V));independent.add(key);row=produced[key]
                L=[1]
                for t in V:L=fastconv(L,[1]*t)
                J=reverse_divided(L,u);d=[sub(x,J[n-1] if n else ZERO) for n,x in enumerate(J)]
                dp=[x if sign(x)>0 else ZERO for x in d]
                assert [list(x) for x in J]==row['J'] and [list(x) for x in dp]==row['positive_primitive']
                for n in range(2,len(dp)-1):cert.add(minor(dp,n))
    assert independent==set(produced) and len(independent)==139
    assert sorted(cert)==[tuple(x) for x in qa['small_scalar_certificate']] and len(cert)==854
    src=(ROOT/'DividedCILaterSmallCertificate.lean').read_text(encoding='utf8')
    lean_rows=[tuple(map(int,x)) for x in re.findall(r'^  \((-?\d+), (-?\d+)\)',src,re.M)]
    assert lean_rows==sorted(cert)
    # Independent small-startup coverage from degree partitions; actual F, not the source helper.
    produced_actual={(z['u'],tuple(z['V']),z['alpha']):z for z in cut['complete_small_actual_contexts']}
    actual_keys=set();integers=set()
    for u in range(3,7):
        for p in parts(u-1):
            if not p:continue
            V=tuple(x+1 for x in p);r=len(V)
            if u+r>=8:continue
            h=sum(p);m=u-1;clamp=(m+h+1)//2
            for alpha in range(1,clamp+1):
                key=(u,V,alpha);actual_keys.add(key);z=produced_actual[key]
                T=alpha+2*u+sum(V);F=arm_prefix(alpha,[2]*u+list(V),T+5)
                D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
                ell=D.index(max(D));margins=[]
                assert ell-r-2==z['first_A_mode'] and clamp==z['clamp']
                for N in range(m+r+2,ell+1):
                    M=D[N]**2-D[N-1]*D[N+1];assert M>=0;margins.append(M);integers.add(M)
                assert margins==z['margins']
    assert actual_keys==set(produced_actual) and len(actual_keys)==41
    assert sorted(integers)==cut['complete_small_actual_integer_margins'] and len(integers)==88
    match=re.search(r'def actualStartupMargins : List ℤ := \[([^]]*)\]',src)
    assert match and list(map(int,match.group(1).split(', ')))==sorted(integers)
    files=['divided_CI_later_primitive_proof.tex','golden_signed_primitive_cut_closure.tex',
        'actual_all_padding_CI_entrance.tex','DividedCILaterPrimitive.lean','DividedCILaterPrimitive.log',
        'GoldenPrimitiveCut.lean','GoldenPrimitiveCut.log','DividedCILaterSmallCertificate.lean',
        'DividedCILaterSmallCertificate.log','audit_divided_CI_later_primitive.py',
        'audit_divided_CI_later_primitive.json','audit_all_padding_primitive_cut.py',
        'audit_all_padding_primitive_cut.json','emit_divided_CI_later_small_certificate.py',
        'verify_all_padding_CI_entrance.py','padding_three_local_prefix_verification.json',
        'padding_three_local_prefix_proof.tex','lc_positive_primitive_window_closure.tex',
        'infinite_padding_full_deficit_LC.tex','binary_CI_infinite_padding_entrance.tex',
        'divided_CI_surplus_three_primitive_proof.tex','binary_CI_two_seed_closure_workbench.tex',
        'sharpened_multitail_single_entrance.tex','homogeneous_reference_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_ALL_PADDING_CI_ENTRANCE_AND_COMPLETE_ACTUAL_LATE_C',
        new_scoped_reports=14,kernels=kernels,
        repaired_primitive='For EVERY CI L=prod[t], t>=3, degree h, EVERY u>=h+1, J=((1+z)^u L-(1-phi)^u L(-phi))/(1+qz) has positive first difference LC at EVERY centre n>=2 on its ENTIRE support. Primitive centre1 may fail and is NOT asserted. Proof: weakened window closure inheriting centres n>=t+1 from a primitive with rank0 deleted; DOUBLE robust LC-numerator head for u>=12; exact CI spectral norm <=2q; improved nonempty/empty junctions; two explicit long-single-interval endpoints; COMPLETE139 low-u exceptions.',
        generic_cut='For ANY finite positive LC b whose positive primitive is LC after deleting rank0, ANY integer a>=0, x_n=sum(j>=1)q^j b_(n+j), E_n=b_n+q b_(n-1), the positive part of x_n-E_(n-a) is LC at EVERY a+2<=n<FIRSTbmode. Exact q^2 cut is a convolution of signed primitive with an LC bilateral geometric/constant/final-q^3 kernel. Negative future primitive contributes one geometric term, rank0 vanishes beyond a, and subtracting a nonnegative constant after geometric normalization preserves LC. This requires the primitive of b ITSELF; the older generic counter only controls primitive(E).',
        analytic='For EVERY CI L of degree h, EVERY m>=h, EVERY alpha>=1, A=(L*sum(k=0..m)(z+z^2)^k-z^(m+alpha)(1+z)^(m+1)L)^+ is coefficient LC at EVERY centre m<=n<=FIRST_A_mode. Uses repaired primitive and cut closure, exact one-coefficient true-source normalization defect, source LR mode bound and uniform first/second startup minors at w=m+1+lenL>=8. COMPLETE41 remaining small-w contexts use exact analytic padding clamp, with all88 distinct integer margins kernel checked.',
        actual='For EVERY ACTUAL sorted tail V>=3, degree h, length r, weight W=h+r, EVERY binary count u>=h+1 and EVERY padding alpha>=1, positive slopes are LC at ALL MOVING centres u+r+1<=N<FIRSTDmode. EVERY C shift R>=3 holds at EVERY current rank N>=W+1. SINGLE entry m=h is now PROVED FOR ALL PADDINGS, then previously proved fixed-padding count propagation and TWO ordinary-F/read joining supply all counts/ranks/shifts in this late range. No finite CI degree/count/capacity/padding cutoff.',
        finite_reduction='The previously open arbitrary-padding entrance at u=h+1 is NOW CLOSED ENTIRELY; the residual alpha4..h is EMPTY. To obtain COMPLETE general C one still needs earlier reference C at N<=W and shorter binary counts u<h+1 (finite for EACH fixed V but unbounded over tails). General C/A2 and ORIGINAL unamplified UI remain OPEN.',
        finite_certificates='Independent COMPLETE139 low-u CI contexts reconstructed by a separate capacity grammar AND reverse polynomial division; all1653 later primitive minors,854 distinct Q(phi) margins. Independent COMPLETE41 small-w/analytic-padding-clamp contexts reconstructed using literal ACTUAL F and D rather than the signed-source helper; all135 coefficient comparisons,88 distinct integer margins. ALL margins checked by ordinary Lean reduction at a proved rational golden-root interval, no native reduction. Finite certificates cover only explicitly bounded exceptions to written unbounded proofs.',
        formal_scope='FOURTEEN NEW scoped reports: SEVEN DividedCILaterPrimitive scalar/power/double-budget/junction kernels, FOUR GoldenPrimitiveCut scalar cut/constant-LC/startup kernels, THREE DividedCILaterSmallCertificate fine golden-root/all854 scalar/complete88 integer certificates (last is AXIOM FREE). Prior global ordinary/window/ULC/Frechet/source/count/read kernels reused WITHOUT recounting. Weak-window, LC convolution and signed-tail assembly, capacity grammar, polynomial identities and actual-model identification are WRITTEN, not end-to-end Lean formalization of all compositions.',
        remaining='Earlier arbitrary-tail reference C N<=W; shorter binary counts 0<=u<h+1; general C/A2; original mixed/incoming/BOTH-rising deep branches and ORIGINAL general unamplified UI remain OPEN. The still stronger FULL primitive assertion including centre1 at u=h+1 is FALSE. Finite-padding geometric-deficit LC is not used as an unproved substitute. No original least-counterexample numerical bound upgrade; first unresolved general-C count6 unchanged.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',primitive_QA=expected,cut_QA=cutexpected,
        independent_complete_small_CI_contexts=139,independent_complete_actual_startup_contexts=41,
        kernel_checked_Qphi_margins=854,kernel_checked_integer_startup_margins=88,
        primitive_state_sha256=qa['state_sha256'],cut_state_sha256=cut['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'all_padding_CI_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
