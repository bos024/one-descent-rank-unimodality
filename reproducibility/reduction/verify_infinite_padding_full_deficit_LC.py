"""Register the whole infinite-padding deficit tail, with explicit scope."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent


def main():
    src=(ROOT/'InfinitePaddingFullDeficit.lean').read_text(encoding='utf8')
    log=(ROOT/'InfinitePaddingFullDeficit.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    names=['golden_upper_five_eighths','final_ulc_factor_payment',
        'entire_final_geometric_power_bound','final_large_kernel_quantitative_margin',
        'twelve_small_final_rows']
    assert log.count('depends on axioms:')==len(names)
    kernels={}
    for name in names:
        hit=re.search(r"'InfinitePaddingFullDeficit\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert hit,name
        axioms={x.strip() for x in hit.group(1).split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
        kernels[name]=sorted(axioms)
    qa=json.loads((ROOT/'audit_infinite_padding_full_deficit_LC.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_WRITTEN_WHOLE_INFINITE_PADDING_DEFICIT_LC'
    expected=dict(exact_final_quotient_kernel_row_budgets=7257,
        exact_generic_LC_last_centre_budgets=1200,exact_entire_positive_deficit_support_reads=362443,
        exact_entire_deficit_LC_tail_minors=359943,exact_new_bridge_centre_minors=2500,
        actual_CI_contexts=2500,actual_exact_single_entrance_contexts=1250)
    assert qa['counts']==expected
    assert qa['state_sha256']=='5f67016146d2a88b5773c9166e77b79115d464b13a3e80b78ed137d1612f3cf1'
    obstruction=json.loads((ROOT/'probe_generic_geometric_cut_LC.json').read_text(encoding='utf8'))
    assert obstruction['status']=='DISPROVED_GENERIC_GEOMETRIC_CUT_LC_BY_EXACT_FIXED_COUNTER'
    assert obstruction['fixed_counter']['margin']==[-205686371365,127116786985]
    files=['infinite_padding_full_deficit_LC.tex','InfinitePaddingFullDeficit.lean',
        'InfinitePaddingFullDeficit.log','audit_infinite_padding_full_deficit_LC.py',
        'audit_infinite_padding_full_deficit_LC.json','verify_infinite_padding_full_deficit_LC.py',
        'binary_CI_infinite_padding_entrance.tex','binary_CI_infinite_padding_entrance_verification.json',
        'generic_geometric_cut_obstruction.tex','probe_generic_geometric_cut_LC.py',
        'probe_generic_geometric_cut_LC.json']
    out=dict(status='PASS_UNBOUNDED_ENTIRE_CI_INFINITE_PADDING_GEOMETRIC_DEFICIT_LC',
        new_scoped_reports=5,kernels=kernels,
        analytic='EVERY CI L=prod[t], all t>=3, h=sum(t-1), EVERY m>=h: b_n=phi*C_(n-1)-C_n for C=L*sum_(k=0)^m(z+z^2)^k is POSITIVE on m+1..degC+1, zero after, and ordinary LC at EVERY centre n>=m+2. Truncating b below m+1 gives a globally nonnegative LC finite polynomial. This extends the registered critical-band deficit LC to the ENTIRE tail, including the previously missing centre m+h+1.',
        proof_extension='The FINAL binomial-division kernel row s=u-1 pays EVERY k=0..u-1. For u>=6 a uniform margin >=(7/180)Q_k follows from ULC factor>=1/2, Q_(u-1)>=3/2 and unbounded geometric-power decay <=32/45; twelve exact small margins close u3..5. Cauchy-Binet and deg L<=u-1 pay the last robust centre without any L1 bound there. The old CI amplitude pays the alternating atom. Binary deficit truncation is globally LC; LC convolution handles all later centres, joining the newly extended finite bridge.',
        formal_scope='FIVE NEW clean standard-axiom scoped reports: golden-root rational bound; full final-ULC-factor inequality; ENTIRE arbitrary-natural-length geometric-power estimate; quantitative final-row scalar payment; all twelve small exact margins. Polynomial quotient, Cauchy-Binet and full-tail convolution/support assembly are WRITTEN, not end-to-end actual-polynomial Lean proofs. Existing row144 integration kernels reused without recounting.',
        obstruction='An exact NON-CI auxiliary counterexample disproves the hoped-for finite geometric-cut closure from global b-LC plus positive-primitive-LC of E=(1+qz)b alone, even BEFORE the first A mode. It is not an actual CI or original conjecture counterexample. Actual clipped-deficit LC through the first A mode remains OPEN.',
        remaining='Finite short-padding single entrance alpha1..h at u=h+1 remains OPEN, along with earlier reference C N<=W, shorter binary counts, general actual C/A2 and ORIGINAL general unamplified UI. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,
        state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'infinite_padding_full_deficit_LC_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
