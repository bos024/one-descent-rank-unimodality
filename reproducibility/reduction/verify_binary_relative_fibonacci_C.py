"""Record complete binary C, retaining explicit formal and original scope."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent


def main():
    kernels = {'BinaryRelativeFibonacci':7,'FibonacciDensityC':13}
    files = ['binary_relative_fibonacci_and_complete_C.tex',
             'audit_binary_relative_fibonacci_C.py','audit_binary_relative_fibonacci_C.json',
             'audit_binary_C_product_consequences.py','audit_binary_C_product_consequences.json',
             'verify_binary_relative_fibonacci_C.py','RegularizedFibonacciEnvelope.lean',
             'RegularizedFibonacciEnvelope.log','C_to_coupled_S_rising_window.tex',
             'CToCoupledSRisingWindow.lean','ClippedForwardRatio.lean',
             'zero_head_C_bridge.tex','UntruncatedOppositeZeroHead.lean']
    for name,n in kernels.items():
        log = (ROOT/(name+'.log')).read_text(encoding='utf8')
        assert log.count('depends on axioms:')+log.count('does not depend on any axioms') == n
        assert not any(x in log for x in ['error:','warning:','sorryAx','ofReduceBool','failed'])
        source = (ROOT/(name+'.lean')).read_text(encoding='utf8')
        assert not re.search(r'^\s*(axiom|sorry|admit)\b',source,re.M)
        files += [name+'.lean',name+'.log']
    q = json.loads((ROOT/'audit_binary_relative_fibonacci_C.json').read_text(encoding='utf8'))
    assert q['status'] == 'PASS_EXACT_BINARY_RELATIVE_FIBONACCI_AND_C_QA'
    assert q['counts'] == dict(actual_terminal_trims=2950,actual_relative_LC=158598,
        arbitrary_trims=35000,arbitrary_tail_LC=1029745,arbitrary_strict_tail_LC=994745,
        arbitrary_relative_LC=2202245,exact_model_polynomial_coefficients=13572,
        exact_model_scalar_payments=1416,rational_density_C=305839,actual_binary_C=3839164)
    p = json.loads((ROOT/'audit_binary_C_product_consequences.json').read_text(encoding='utf8'))
    assert p['status'] == 'PASS_EXACT_ALL_DEPTH_BINARY_C_PRODUCT_CONSEQUENCES_QA'
    assert p['counts'] == dict(actual_pairs=6000,both_rising_source_ratio_minors=424703,
        nonnegative_current_both_rising_nonrecoveries=238410,
        beyond_fifth_and_old_diagonal_nonrecoveries=150385,
        proper_zero_head_integer_budget_payments=17661)
    out = dict(status='PASS_UNBOUNDED_BINARY_RELATIVE_FIBONACCI_AND_COMPLETE_C',
        new_scoped_reports=sum(kernels.values()),kernels=kernels,
        binary_C='ALL actual 1alpha2^h, alpha>=1,h>=1, ALL ranks and shifts R>=3 on the positive ordinary slope prefix. No bound on count, capacity-word length, initial padding or overlap depth.',
        larger_abstract_family='Every arbitrary-last-trimmed Fibonacci convolution history from [1] has exact prefix and strict integer LC tail, hence d/Fibonacci relative LC. Every positive-support derivative sequence D2=D3=1 with Fibonacci-relative LC satisfies own-C at ALL shifts; no actual cumulative LC assumed.',
        proof='Exact binary append changes ONLY the last raw positive-D coefficient. Unbounded trim induction supplies strict tail minors; Cassini and componentwise Fibonacci bounds transfer to relative LC. Current density ratio a gives LR domination over a one-parameter deformed Fibonacci model. Two cumulative sums preserve LR. Alternating model coefficients paired via jA>=(j+1)B, unbounded power-gap induction and positive Cassini endpoints pay all model C comparisons; Fibonacci recurrence propagates all shifts.',
        both_rising_consequence='ENTIRE first-missing-weight3 branch at ALL opposite first weights/counts/capacities/padding/depths: BOTH ordinary factors still rising/current deficit>=0 imply NONRECOVERY. Usual OLD head/proper S hypotheses retained. Sole nonbinary one-capacity firstweight3 arm has flat positiveD and is paid directly.',
        zero_head_consequence='ENTIRE properly conditioned zero-head S with both counts>=2 and EITHER first missing weight3, NO OLD A2, NO phase/depth/opposite-first-weight bounds. Existing double-defect phase forcing plus new binary C proves this, not a new universal unrestricted S assertion.',
        formal_scope='20 NEW clean scoped reports. FULL arbitrary-trim LC-tail induction and relative-minor transfer are kernel checked under explicit support/prefix/append hypotheses. All unbounded power-pair/Fibonacci coefficient/endpoint/LR/scalar transfer kernels are checked. Word-to-history identification, polynomial coefficient assembly, final abstract C and actual composition assembly are complete WRITTEN proofs, NOT one end-to-end Lean theorem. Finite QA does not prove unbounded quantifiers.',
        remaining='General C for nonbinary capacity words with >=6 non-one parts OPEN. Remaining mixed c0/incoming, general higher-first-weight both-rising complement, A2 and ORIGINAL unamplified coefficient unimodality OPEN. Binary ceased-rising opposite-phase branch not globally closed by this theorem. No original least-counterexample count upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'binary_relative_fibonacci_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__ == '__main__':
    main()
