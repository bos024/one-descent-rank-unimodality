"""Register alpha three only after complete finite coverage and clean kernels."""
from pathlib import Path
from itertools import combinations_with_replacement
import json,hashlib,re
from verify_divided_CI_surplus_three_primitive import kernel
from audit_joint_structure import fastconv
from probe_divided_CI_positive_primitive import divided
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign
from audit_binary_CI_infinite_padding_entrance import minor
ROOT=Path(__file__).resolve().parent
P=[1,1,2,1];ZERO=(0,0)

def main():
    kernels={}
    kernels['PaddingThreeLocalPrefix']=kernel('PaddingThreeLocalPrefix',[
        'relaxed_first_row_margin','relaxed_interior_row_zero','relaxed_final_row_power',
        'binary_second_primitive_head','concave_junction_scalar',
        'unperturbed_interval_junction_gap','exact_perturbed_last_junction'])
    kernels['PaddingThreeSmallCertificate']=kernel('PaddingThreeSmallCertificate',[
        'golden_fine_interval','all_scalar_margins'])
    qa=json.loads((ROOT/'audit_padding_three_local_prefix.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_LOCAL_CI_PREFIX_AND_ACTUAL_PADDING_THREE'
    expected=dict(complete_small_positive_read_coefficients=165,complete_small_both_prefix_minors=106,
        complete_binary_eight_full_support_minors=9,exact_padding_three_binary_second_heads=143,
        exact_padding_three_binary_entire_ordinary_and_primitive_minors=11440,
        exact_relaxed_generic_robust_all_prefix_minors=32758,generic_LC_numerators_with_relaxed_budget=1000,
        exact_padding_three_append_quotient_identities=1200,exact_padding_three_robust_X_head_minors=73053,
        exact_padding_three_junction_lower_bounds=1175,exact_padding_three_both_local_prefix_minors=73053,
        exact_local_prefix_truncation_window_minors=73053,padding_three_CI_induction_contexts=1200,
        exact_padding_three_actual_head_identities=22896,exact_padding_three_actual_through_first_mode_LC_minors=18686,
        exact_padding_three_all_read_prefix_minimum_C_payments=46192,actual_padding_three_entry_contexts=400)
    assert qa['counts']==expected
    assert qa['state_sha256']=='752519988de4d2480004bc4fe34aed9c8ac4e7ad83cdadb1f83da72c64a7bb25'
    # A distinct exhaustive grammar, not the producer's recursive partitions.
    actual={(row['u'],tuple(row['degree_partition'])):row for row in qa['small_contexts']}
    independent=set();cert=set()
    for u in range(1,8):
        for length in range(4):
            for V in combinations_with_replacement(range(3,8),length):
                if sum(t-1 for t in V)>u-1:continue
                key=(u,tuple(t-1 for t in V));independent.add(key);row=actual[key]
                L=[1]
                for t in V:L=fastconv(L,[1]*t)
                _,J=divided(fastconv(L,P),u)
                d=[sub(x,J[n-1] if n else ZERO) for n,x in enumerate(J)]
                dp=[x if sign(x)>0 else ZERO for x in d];K=u-2
                assert [list(x) for x in J]==row['J'] and [list(x) for x in dp]==row['positive_primitive']
                for n in range(K+2):cert.add(sub(mul((100,0),J[n]),(1,0)))
                for n in range(1,K+1):cert.add(minor(J,n));cert.add(minor(dp,n))
    assert independent==set(actual) and len(independent)==30
    _,J=divided(P,8);d=[sub(x,J[n-1] if n else ZERO) for n,x in enumerate(J)]
    dp=[x if sign(x)>0 else ZERO for x in d]
    for x in J:cert.add(sub(mul((100,0),x),(1,0)))
    for n in range(1,len(J)-1):cert.add(minor(J,n));cert.add(minor(dp,n))
    assert sorted(cert)==[tuple(x) for x in qa['small_scalar_certificate']]
    src=(ROOT/'PaddingThreeSmallCertificate.lean').read_text(encoding='utf8')
    lean_rows=[tuple(map(int,x)) for x in re.findall(r'^  \((-?\d+), (-?\d+)\)',src,re.M)]
    assert lean_rows==sorted(cert) and len(lean_rows)==399
    files=['padding_three_local_prefix_proof.tex','actual_padding_three_CI_entrance.tex',
        'PaddingThreeLocalPrefix.lean','PaddingThreeLocalPrefix.log',
        'PaddingThreeSmallCertificate.lean','PaddingThreeSmallCertificate.log',
        'audit_padding_three_local_prefix.py','audit_padding_three_local_prefix.json',
        'emit_padding_three_small_certificate.py','verify_padding_three_local_prefix.py',
        'weighted_divided_CI_padding_one_verification.json','weighted_divided_CI_padding_one_proof.tex',
        'actual_padding_one_CI_entrance.tex','divided_CI_surplus_three_primitive_verification.json',
        'infinite_padding_full_deficit_LC.tex','binary_CI_infinite_padding_entrance.tex',
        'lc_positive_primitive_window_closure.tex','binary_CI_two_seed_closure_workbench.tex',
        'sharpened_multitail_single_entrance.tex','homogeneous_reference_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_LOCAL_CI_PREFIX_AND_ACTUAL_PADDING_THREE_LATE_C',
        new_scoped_reports=9,kernels=kernels,
        analytic='For EVERY CI L=prod[t], t>=3, degree h, EVERY u>=h+1, P3=1+z+2z^2+z^3, c=q^2(1-phi)^u L(-phi), J=(P3(1+z)^u L-c)/(1+qz) is positive through u-1, ordinary LC at every prefix centre 1..u-2, and its positive primitive is LC at those same centres. Global ordinary LC is NOT needed. Proof uses LOCAL two-property prefix truncation/window closure, relaxed robust LC-numerator budget with first coefficient <=(v+3)/2 and ALL centres 1..v-1 for v>=7, absorption R=(1+z)P3=(1,2,3,3,1), unbounded binary base and simultaneous interval induction with last junction >=1+u/6.',
        actual='For EVERY ACTUAL sorted tail V>=3, degree h, length r, weight W=h+r, EVERY binary count u>=h+1 at padding alpha=3, positive slopes are LC at ALL moving centres u+r+1<=N<FIRSTDmode and EVERY C shift R>=3 holds at EVERY N>=W+1. SINGLE entry m=h follows from exact raw deficit=primitive(J) ONLY at offsets s>=1, first-mode bound, backward integration and the existing TWO strict actual seeds with alpha3 defects; fixed-padding count/read joining gives all larger counts.',
        finite_reduction='At u=h+1 the remaining short-padding entrance set is NOW ONLY 4<=alpha<=h. Alpha1,alpha2,alpha3 and alpha>=h+1 are proved at EVERY CI degree; no remaining short alpha is silently included.',
        finite_certificate='Independent COMPLETE enumeration of all 30 CI contexts with 1<=u<=7,h<=u-1<=6 plus the binary u8 full-support base. A separate combinations-with-replacement capacity grammar reconstructs every context and scalar margin. ALL399 distinct Q(phi) scalar margins are verified by ordinary Lean Boolean reduction at certified rational golden-root endpoints; no native reduction. This finite certificate covers ONLY the explicitly bounded exceptions to the unbounded proof.',
        formal_scope='NINE NEW scoped standard-axiom reports: seven PaddingThreeLocalPrefix kernels for relaxed first/interior/final robust row payments, complete arbitrary-real binary second head, concave junction scalar and its quotient-ratio payment, exact perturbed junction; two PaddingThreeSmallCertificate kernels for the fine golden-root interval and all399 exact scalar margins. Previous first-primitive/window/ULC/actual-seed/backward/count/read kernels reused WITHOUT recounting. Polynomial identities, local truncation/window proof, small capacity grammar, whole CI assembly and actual-arm identification are WRITTEN, not an end-to-end actual-composition Lean proof.',
        remaining='Short paddings 4<=alpha<=h at the single entrance, earlier reference C N<=W, shorter binary counts, general C/A2 and ORIGINAL general unamplified UI remain OPEN. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,
        independent_complete_small_contexts=30,kernel_checked_scalar_margins=399,
        state_sha256=qa['state_sha256'],sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'padding_three_local_prefix_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
