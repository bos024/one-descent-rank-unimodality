"""Register the weighted CI prefix and the actual alpha-one late-C theorem."""
from pathlib import Path
import json,hashlib
from verify_divided_CI_surplus_three_primitive import kernel
ROOT=Path(__file__).resolve().parent

def main():
    kernels=kernel('WeightedDividedCI',['ordinary_first_head','binary_first_primitive_head',
        'binary_second_primitive_head','nonempty_first_primitive_head',
        'unperturbed_interval_junction_gap','exact_perturbed_last_junction'])
    qa=json.loads((ROOT/'audit_weighted_divided_CI_padding_one.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_WEIGHTED_CI_PREFIX_AND_ACTUAL_PADDING_ONE_ENTRANCE'
    expected=dict(exact_small_weighted_binary_bases=5,exact_weighted_binary_first_head_payments=149,
        exact_weighted_binary_constant_update_identities=149,exact_entire_weighted_binary_positive_primitive_minors=11175,
        exact_weighted_binary_second_head_payments=145,exact_entire_weighted_CI_ordinary_LC_minors=120123,
        exact_weighted_ordinary_first_head_payments=1200,exact_weighted_interval_append_quotient_identities=1200,
        exact_weighted_low_primitive_source_identities=17832,exact_weighted_robust_X_head_minors=61216,
        exact_weighted_quantitative_last_junction_payments=1158,exact_weighted_actual_first_primitive_payments=1200,
        exact_weighted_CI_positive_primitive_prefix_minors=61216,exact_prefix_window_boundary_minors=218125,
        weighted_CI_induction_contexts=1200,exact_padding_one_primitive_head_identities=19430,
        exact_actual_padding_one_through_first_mode_LC_minors=15220,
        exact_padding_one_all_read_prefix_minimum_C_payments=39260,actual_padding_one_entry_contexts=400)
    assert qa['counts']==expected
    assert qa['state_sha256']=='3209121fac0270a3dc8665b0aed9d988cf8ffe320f4c370600f88d93d4ab3d05'
    assert qa['postmode_negative_control']==dict(V=[4,32],m=34,alpha=19,first_A_mode=61,n=63,
        minor=[92474729448806994408,-59412110474266913988])
    files=['weighted_divided_CI_padding_one_proof.tex','actual_padding_one_CI_entrance.tex',
        'padding_one_weighted_division_research_notes.tex','WeightedDividedCI.lean','WeightedDividedCI.log',
        'audit_weighted_divided_CI_padding_one.py','audit_weighted_divided_CI_padding_one.json',
        'verify_weighted_divided_CI_padding_one.py','verify_divided_CI_surplus_three_primitive.py',
        'divided_CI_surplus_three_primitive_verification.json','actual_padding_two_CI_entrance.tex',
        'binary_CI_two_seed_closure_workbench.tex','binary_CI_infinite_padding_entrance.tex',
        'infinite_padding_full_deficit_LC.tex','lc_positive_primitive_window_closure.tex',
        'sharpened_multitail_single_entrance.tex','homogeneous_reference_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_WEIGHTED_CI_PRIMITIVE_PREFIX_AND_ACTUAL_PADDING_ONE_LATE_C',
        new_scoped_reports=6,kernels=kernels,
        analytic='For EVERY CI L=prod[t], t>=3, degree h, and EVERY u>=h+1, the WEIGHTED divided quotient J=(((2+z)(1+z)^u L)-c)/(1+qz), c=q^2(1-phi)^u L(-phi), is a positive globally LC polynomial and its POSITIVE primitive is LC at EVERY prefix centre 1<=n<=u-2. No degree/count/capacity cutoff. Proof: all-length weighted binary base, generic primitive-window PREFIX extension, independent global ordinary first-head payment, exact interval quotient correction and robust perturbed junction >=4+11u/15.',
        actual='For EVERY ACTUAL sorted tail V>=3, degree h, length r, weight W=h+r, EVERY binary count u>=h+1, at padding alpha=1 the actual positive slopes are LC at all MOVING centres u+r+1<=N<FIRSTDmode; EVERY actual C shift R>=3 holds at EVERY N>=W+1. Proof uses SINGLE entry m=h, exact raw deficit=primitive(weighted J) ONLY for offsets s>=1, first-mode upper bound, backward integration through correctly scoped head, the existing TWO strict ACTUAL seeds with padding-one defects, then previously proved fixed-padding count propagation and ordinary-F/read joining.',
        finite_reduction='At entry u=h+1 the remaining arbitrary-padding entrance set is NOW ONLY 3<=alpha<=h. Alpha1 and alpha2 are proved at EVERY CI degree, and alpha>=h+1 was already proved. This does NOT establish the remaining short paddings.',
        formal_scope='SIX NEW scoped standard-axiom reports in WeightedDividedCI: ordinary first head, weighted binary primitive first and second heads, correctly normalized nonempty first primitive head, unperturbed weighted junction gap and exact perturbed junction. Prior window/quotient/CI-induction/backward-integration/actual-seed/count/read kernels reused WITHOUT recounting. Prefix-window proof, polynomial identities, spectral estimates, entire CI assembly and identification of actual arms are WRITTEN, not end-to-end Lean formalization. Exact QA independently checks the displayed identities; finite nonfailures are not used as a universal proof.',
        remaining='Residual single-entry paddings 3<=alpha<=h; arbitrary early reference C N<=W; shorter binary counts; general C/A2 and ORIGINAL general unamplified UI all OPEN. General arbitrary-padding full-head deficit LC is FALSE after the first mode, even at exact entry: V=[4,32],m=h=34,alpha19,n63>mode61 has exact negative Q(phi) minor. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,
        state_sha256=qa['state_sha256'],postmode_negative_control=qa['postmode_negative_control'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'weighted_divided_CI_padding_one_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
