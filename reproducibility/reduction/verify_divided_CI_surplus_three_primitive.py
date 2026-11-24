"""Register the unbounded divided-CI primitive theorem and ACTUAL padding two."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent


def kernel(module,names):
    src=(ROOT/(module+'.lean')).read_text(encoding='utf8')
    log=(ROOT/(module+'.log')).read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    assert log.count('depends on axioms:')==len(names)
    out={}
    for name in names:
        hit=re.search("'"+module+r"\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert hit,(module,name)
        ax={x.strip() for x in hit.group(1).split(',') if x.strip()}
        assert ax<={'propext','Classical.choice','Quot.sound'},(module,name,ax)
        out[name]=sorted(ax)
    return out


def main():
    kernels={}
    kernels['DividedCIPrimitive']=kernel('DividedCIPrimitive',[
        'binary_first_primitive_head','binary_second_primitive_head',
        'nonempty_first_primitive_head','unperturbed_interval_junction_gap',
        'exact_perturbed_last_junction','entire_capacity_word_induction'])
    kernels['BinaryCITwoSeed']=kernel('BinaryCITwoSeed',[
        'first_Cassini_seed_strict','second_Cassini_seed_full_parameter_bound',
        'positive_part_preserves_strict_seed'])
    qa=json.loads((ROOT/'audit_divided_CI_surplus_three_primitive.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_SURPLUS_THREE_PRIMITIVE_AND_ACTUAL_PADDING_TWO_ENTRANCE'
    expected=dict(exact_small_binary_primitive_bases=3,exact_entire_binary_positive_primitive_minors=11026,
        exact_binary_first_head_payments=147,exact_binary_constant_update_identities=147,
        exact_binary_second_head_payments=145,exact_entire_interval_append_quotient_identities=1200,
        exact_all_low_primitive_source_identities=17979,exact_robust_head_X_minors=62681,
        exact_quantitative_last_junction_payments=1200,exact_actual_first_primitive_seed_payments=1200,
        exact_entire_divided_CI_positive_primitive_minors=119264,independent_CI_interval_induction_contexts=1200,
        exact_padding_two_divided_primitive_head_identities=21103,
        exact_actual_padding_two_through_first_mode_LC_minors=16296,
        exact_actual_padding_two_all_read_prefix_minimum_C_payments=42606,actual_padding_two_contexts=400)
    assert qa['counts']==expected
    assert qa['state_sha256']=='1a2f47deea5c05e9d0d8a6a9a2f94bc5ff1dd384252389dfd46b3c1baf3aa0a3'
    seeds=json.loads((ROOT/'audit_binary_CI_tail_and_two_seeds.json').read_text(encoding='utf8'))
    assert seeds['status']=='PASS_EXACT_SIGNED_BINARY_CI_TAIL_IDENTITIES_AND_ENTIRE_TWO_SEED_FORMULAS'
    assert seeds['counts']==dict(all_signed_actual_tail_coefficients_including_negative_tail=255857,
        unbounded_seed_formula_instances_exact_QA=1618,actual_tail_contexts=2400)
    assert seeds['sha256']=='3a77efe9c0c63f3088f1f8e58049d534cf77919a2ff95f16c8eebd73e7f53956'
    files=['divided_CI_surplus_three_primitive_proof.tex','actual_padding_two_CI_entrance.tex',
        'finite_padding_divided_CI_primitive.tex','DividedCIPrimitive.lean','DividedCIPrimitive.log',
        'BinaryCITwoSeed.lean','BinaryCITwoSeed.log','binary_CI_two_seed_closure_workbench.tex',
        'audit_divided_CI_surplus_three_primitive.py','audit_divided_CI_surplus_three_primitive.json',
        'audit_binary_CI_tail_and_two_seeds.py','audit_binary_CI_tail_and_two_seeds.json',
        'verify_divided_CI_surplus_three_primitive.py',
        'probe_divided_CI_positive_primitive.py','probe_finite_padding_geometric_deficit.py',
        'probe_ci_primitive_full_LC.py','probe_binary_CI_two_seed_closure.py',
        'binary_CI_infinite_padding_entrance.tex','infinite_padding_full_deficit_LC.tex',
        'lc_positive_primitive_window_closure.tex','sharpened_multitail_single_entrance.tex',
        'homogeneous_reference_complete_C.tex','lc_positive_primitive_window_closure_verification.json',
        'infinite_padding_full_deficit_LC_verification.json']
    out=dict(status='PASS_UNBOUNDED_DIVIDED_CI_POSITIVE_PRIMITIVE_AND_ACTUAL_PADDING_TWO_LATE_C',
        new_scoped_reports=9,brand_new_reports=6,previously_unregistered_seed_reports_first_counted=3,
        kernels=kernels,
        analytic='For EVERY CI L=prod[t], all t>=3, degree h, and EVERY U>=h+3, J=((1+z)^U L-((1-phi)^U L(-phi)))/(1+qz) is a positive ordinary-LC finite polynomial AND its positive first difference is LC on its ENTIRE support. No count/capacity/degree cutoff. New proof uses all-length binary head induction, exact interval-append quotient identity, generic nonsymmetric primitive-window closure, robust low-head coefficient budget and quantitative last junction >=1+U/30.',
        actual='For EVERY ACTUAL sorted tail V>=3 of degree h, EVERY binary count u>=h+1, at padding alpha=2, the ACTUAL positive slopes of 1^2 2^u V are LC at MOVING centres u+lenV+1<=N<FIRSTDmode. EVERY actual C shift R>=3 holds at EVERY current N>=W+1. Proof establishes SINGLE entry m=h via exact raw deficit=primitive(J_(h+3,L)) for offsets s>=1, backward integration stopped before the exceptional s0 normalization, and the independently proved TWO strict actual entrance seeds. The prior fixed-padding count induction and TWO ordinary-F/read integration then give all larger counts. Early reference ranks N<=W are NOT included.',
        finite_reduction='At u=h+1 the residual short-padding entrance set shrinks from alpha1..h to alpha=1 OR 3<=alpha<=h. Alpha2 is NOW proved at every CI degree. All alpha>=h+1 were already proved by row145. General arbitrary-padding entrance still OPEN.',
        formal_scope='NINE first-counted scoped standard-axiom reports: SIX new DividedCIPrimitive kernels (both complete arbitrary-real binary primitive heads, correctly normalized nonempty first primitive head, interval junction gap, exact perturbed junction and ENTIRE arbitrary-capacity-word induction); THREE earlier UNREGISTERED BinaryCITwoSeed kernels counted HERE for the first time (both strict actual-entry scalar seeds and positive-part transport). Prior window, robust quotient, spectral, backward integration, homogeneous-reference and binary-count/read-joining kernels reused WITHOUT recounting. Polynomial/source identities, actual mode/head identification, spectral scalar inequalities, whole CI induction assembly and actual composition identification are WRITTEN, not end-to-end actual-arm Lean formalization. Exact QA checks the displayed identities and bounds independently; finite nonfailures are not substituted for the unbounded proof.',
        remaining='Padding alpha1 and alpha3..h at the single entrance remain OPEN, as do arbitrary early reference C N<=W, shorter binary counts, general C/A2 and ORIGINAL general unamplified UI. Stronger divided-CI primitive assertions U>=h+2 or later-centre-only U>=h+1 remain OPEN. Full primitive U=h+1 is FALSE at its first centre. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,seed_QA=seeds['counts'],
        state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'divided_CI_surplus_three_primitive_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
