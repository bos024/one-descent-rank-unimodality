"""Register one unbounded analytic entrance and its precise padding scope."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent


def main():
    src=(ROOT/'BinaryCIInfiniteEntrance.lean').read_text(encoding='utf8')
    log=(ROOT/'BinaryCIInfiniteEntrance.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    names=['backward_geometric_LC_transport','entire_finite_backward_integration',
        'entire_geometric_deficit_LC_bridge','alternating_deficit_robust_budget',
        'first_robust_numerator_seed','kernel_last_row_absorbs_next_numerator',
        'weighted_rows_and_last_LC_absorption']
    assert log.count('depends on axioms:')==len(names)
    kernels={}
    for name in names:
        match=re.search(r"'BinaryCIInfiniteEntrance\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert match,name
        axioms={x.strip() for x in match.group(1).split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
        kernels[name]=sorted(axioms)
    qa=json.loads((ROOT/'audit_binary_CI_infinite_padding_entrance.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_WRITTEN_UNBOUNDED_INFINITE_PADDING_CI_ENTRANCE'
    expected=dict(independent_positive_binomial_expansions=4092,exact_ULC_kernel_minors=4004,
        exact_quantitative_all_read_kernel_budgets=117392,
        exact_generic_LC_numerator_robust_budgets=56749,generic_LC_numerators=1600,
        exact_entire_CI_amplitude_budgets=2400,independent_exact_geometric_deficit_identities=151201,
        exact_LC_geometric_deficit_minors=146401,exact_entire_infinite_padding_CI_tail_LC_minors=312339,
        exact_backward_LC_transport_identities=146401,actual_CI_infinite_padding_contexts=2400,
        exact_large_padding_pre_first_mode_LC_minors=50388,
        exact_large_padding_actual_all_read_prefix_minimum_C_payments=110238,
        large_padding_logical_shift_coverage=18784616,
        actual_large_padding_mode_and_late_C_contexts=800)
    assert qa['counts']==expected
    assert qa['state_sha256']=='706195b547c513ce27289948008efaafe7cc2dab7078eed8f48e00756b79c460'
    files=['binary_CI_infinite_padding_entrance.tex','BinaryCIInfiniteEntrance.lean',
        'BinaryCIInfiniteEntrance.log','audit_binary_CI_infinite_padding_entrance.py',
        'audit_binary_CI_infinite_padding_entrance.json','verify_binary_CI_infinite_padding_entrance.py',
        'binary_ordinary_tail_and_dominant_one_jump_C.tex',
        'sharpened_multitail_single_entrance.tex','multitail_binary_prefix_finite_principle.tex',
        'homogeneous_reference_complete_C.tex']
    out=dict(status='PASS_UNBOUNDED_CI_INFINITE_PADDING_ENTRANCE_AND_HALF_PADDING_REDUCTION',
        new_scoped_reports=7,kernels=kernels,
        analytic='EVERY CI L=prod[t], all t>=3, h=sum(t-1), EVERY m>=h: C=L*sum_(k=0)^m(z+z^2)^k is ordinary LC at EVERY centre n>=m, with no count/capacity/degree bound. NEW proof: Q_u=trunc_(<=u)(1+z)^u/(1+qz) is ULC(u); quantitative all-read kernel plus Cauchy-Binet prove robust LC budget for LQ_u with L0=1, L1<=(u-1)/2. CI spectral amplitude |L(-phi)|q^m<=1 pays alternating geometric deficit. Full finite BACKWARD LC integration from known far tail closes entire bridge; first centre uses old signed Cassini payment.',
        actual='For ACTUAL 1alpha2^uV, h=sum(t-1), u>=h+1 and alpha>=ceil((u-1+h)/2)+1: positive slopes LC at MOVING centres u+lenV+1<=n<FIRSTDmode and ALL-shift actual C at EVERY N>=W+1. Mode bound ceil((3m+h)/2) for the signed tail keeps finite-padding subtraction AFTER infinite-padding first mode; max and first mode unchanged. No claim of LC from fixed W+2 when u>h+1.',
        finite_reduction='At SINGLE entrance u=h+1, EVERY alpha>=h+1 is NOW proved analytically. Thus the all-padding LC premise in row143 reduces from alpha1..2h+2 to JUST alpha1..h. The smaller-padding entrances remain OPEN for arbitrary CI degree. Add those entrances to obtain ALL late actual C at ALL u>=h+1, ALL alpha. Early reference C N<=W and shorter binary counts remain separate inputs for complete C.',
        formal_scope='SEVEN NEW clean standard-axiom scoped reports: scalar backward geometric LC payment; ENTIRE finite backward induction; its ENTIRE composition for arbitrary coefficient/deficit sequences; robust alternating perturbation; full arbitrary-parameter first robust numerator seed; last kernel-row payment; missing next LC numerator coefficient absorption. ULC generation uses only standard Liggett finite-order ULC convolution on Q_(u-1) and [2] (primary theorem Gurvits arXiv0804.1181 Theorem1.1). ULC/binomial kernel and Cauchy-Binet assembly, CI spectral identification, actual global-mode/clamp and C read joining are WRITTEN, not end-to-end actual-composition Lean proof. Exact QA uses independent binomial enumeration of the binary kernel, actual recurrences and Q(phi) comparisons; logical shift coverage is not literal shift enumeration.',
        remaining='Actual entrance alpha<=h at u=h+1 remainsOPEN. Generic two-seed closure, all-s full inverse-kernel LC, arbitrary earlier reference C N<=W, general actual C/A2 and ORIGINAL general unamplified UI remainOPEN. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,
        state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'binary_CI_infinite_padding_entrance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
