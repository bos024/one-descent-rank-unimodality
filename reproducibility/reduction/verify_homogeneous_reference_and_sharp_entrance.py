"""Freeze new universal proofs with their explicit scoped formal boundary."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent


def main():
    src=(ROOT/'HomogeneousReferenceC.lean').read_text(encoding='utf8')
    log=(ROOT/'HomogeneousReferenceC.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    names=['all_capacity_relative_spectral_bound','entire_word_relative_spectral_bound',
        'entire_word_homogeneous_rank_budget','entire_convolution_ratio_envelope',
        'spectral_determinant_nonnegative','alternating_first_defect_LC_boundary',
        'later_ordinary_seed_exact_payment','simultaneous_finite_read_integration']
    assert log.count('depends on axioms:')==len(names)
    kernels={}
    for name in names:
        match=re.search(r"'HomogeneousReferenceC\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert match,name
        axioms={x.strip() for x in match.group(1).split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
        kernels[name]=sorted(axioms)
    qa=json.loads((ROOT/'audit_homogeneous_reference_and_sharp_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_HOMOGENEOUS_REFERENCE_C_AND_SHARP_ENTRANCE_QA'
    counts=dict(all_capacity_relative_spectral_norm_steps=26348,
        exact_binary_cumulative_vs_reference_slope_determinants=48000,
        exact_homogeneous_relative_amplitude_budgets=43928,
        all_read_binary_cumulative_envelopes=841797,
        exact_prefix_minimum_all_shift_C_payments=205644,
        logical_shift_coverage=35797904,literal_all_shift_C_products=228673,
        independently_rebuilt_arbitrary_order_reference_words=4000,
        finite_only_sharpened_rising_tail_LC_minors=66730,
        exact_new_ordinary_and_cumulative_integration_steps=2465104,
        sharpened_actual_contexts=1200)
    assert qa['counts']==counts
    assert qa['state_sha256']=='1e1a3766808ec64213c5e7854c09d36407e30a6a0e55e9a29ccac5ae2630172d'
    files=['homogeneous_reference_complete_C.tex','sharpened_multitail_single_entrance.tex',
        'HomogeneousReferenceC.lean','HomogeneousReferenceC.log',
        'audit_homogeneous_reference_and_sharp_entrance.py',
        'audit_homogeneous_reference_and_sharp_entrance.json',
        'verify_homogeneous_reference_and_sharp_entrance.py',
        'arbitrary_Fibonacci_tail_late_C.tex','ArbitraryFibonacciTailLateC.lean','ArbitraryFibonacciTailLateC.log',
        'multitail_binary_prefix_finite_principle.tex','MultitailCassiniBudget.lean','MultitailCassiniBudget.log',
        'OneJumpUniformAnalyticKernels.lean','OneJumpUniformAnalyticKernels.log']
    out=dict(status='PASS_UNBOUNDED_HOMOGENEOUS_REFERENCE_C_AND_HPLUS1_FINITE_PRINCIPLE',
        new_scoped_reports=8,kernels=kernels,
        reference='EVERY finite capacity word>=2, ANYORDER, after removing all leading twos: W=degB=sumV. COMPLETE ALL-shift reference C at EVERY N>=W+1, improving W+6 to FIRST homogeneous rank. B>=0 and ALL-read binary cumulative ratio envelope, RELATIVE full-word bound phi^r|B(-phi)|<=phi^W B(1/phi). FIRST rank W+1 has negative conjugate error. All remaining ranks use exact determinant and sharp amplitude budget; singleton rank W+2 is exact equality. No early single-jump C theorem imported. General earlier reference ranks N<=W remainOPEN.',
        sharpened_principle='ANY fixed sorted nonempty V>=3, r=len,W=sum,h=W-r,H=h+1: FIRSTDmode ordinary LC only at SINGLEu=H and alpha<=2h+2, centersW+2..FIRSTmode, implies ALLlateactualC atN>=W+1 forEVERYu>=H,ALLalpha. Add early reference C N<=W and shorter actual u<H,alpha<=u+h+1 to obtain COMPLETEC for ALLu. Exact same padding/mode bounds read<=2u+W+1. Alternating signed Cassini pays boundary nonnegatively; zero allowed. TWO explicit ORDINARY F seeds atN0-2/N0-1 replace unnecessarily early D seeds, followed by FULL finite F/G integration. Entrance remains HYPOTHESIS for arbitraryV.',
        actual_band='UNCONDITIONALLY ALL actual C shifts for 1alpha2^uV throughout W+1<=N<=u+r+2; nonempty at u>=h-1. No density/entrance LC hypothesis for this band. First mismatch improves C, not prefix equality at that endpoint.',
        formal_scope='EIGHT NEW clean standard-axiom scoped reports: ALLcapacity relative norm, FULL unbounded word relative-amplitude induction, arbitrary word/rank amplitude budget, ENTIRE finite convolution ratio-envelope transport, spectral scalar determinant payment, alternating-negative-boundary LC payment, exact later ordinary seed identity, FULL arbitrary-length simultaneous F/G finite-read induction. Numerator generation, Binet/atom identification, binary cumulative LC, exact spectral determinant identification/sign joining, actual polynomial/mode/ordinary-seed assembly and whole LC propagation are WRITTEN with old propagation kernels reused, not end-to-end Lean actual-composition proof. QA independently rebuilds references from suffix products. Finite CI LC diagnostics are not a universal entrance proof.',
        remaining='Arbitrary CI inverse-kernel/actual u=h+1 entrance LC remains OPEN. Earlier arbitrary-reference C N<=W, general actualC/A2 and ORIGINAL general unamplified UI remainOPEN. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=counts,
        state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'homogeneous_reference_and_sharp_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
