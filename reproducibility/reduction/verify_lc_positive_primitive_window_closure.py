"""Register only the proved nonsymmetric window/unperturbed quotient closure."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent


def main():
    src=(ROOT/'LowerFrechetLC.lean').read_text(encoding='utf8')
    log=(ROOT/'LowerFrechetLC.log').read_text(encoding='utf8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    names=['decreasing_lower_frechet_payment','entire_lower_frechet_LC_clipping']
    assert log.count('depends on axioms:')==len(names)
    kernels={}
    for name in names:
        hit=re.search(r"'LowerFrechetLC\."+name+r"' depends on axioms: \[([^]]*)\]",log)
        assert hit,name
        ax={x.strip() for x in hit.group(1).split(',') if x.strip()}
        assert ax<={'propext','Classical.choice','Quot.sound'},(name,ax)
        kernels[name]=sorted(ax)
    qa=json.loads((ROOT/'audit_lc_positive_primitive_window_closure.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_EXACT_QA_WRITTEN_NONSYMMETRIC_WINDOW_AND_UNPERTURBED_QUOTIENT_PRIMITIVE_LC'
    expected=dict(exact_nonsymmetric_uniform_window_primitive_minors=148508,
        nonsymmetric_window_contexts=7000,exact_weighted_binary_primitive_minors=60104,
        weighted_binary_contexts=3500,exact_ordinary_LC_quotient_product_minors=466837,
        exact_quotient_product_positive_primitive_minors=227042,CI_quotient_product_contexts=6600,
        exact_non_golden_rational_quotient_primitive_minors=47264,
        arbitrary_rational_q_CI_quotient_contexts=1600)
    assert qa['counts']==expected
    assert qa['state_sha256']=='fa079a69da7f88013f85d625bbc0ae97c4ea46cd0836c55f5a86353f176e68be'
    files=['lc_positive_primitive_window_closure.tex','LowerFrechetLC.lean','LowerFrechetLC.log',
        'audit_lc_positive_primitive_window_closure.py','audit_lc_positive_primitive_window_closure.json',
        'verify_lc_positive_primitive_window_closure.py','binary_CI_infinite_padding_entrance.tex']
    out=dict(status='PASS_UNBOUNDED_NONSYMMETRIC_WINDOW_AND_UNPERTURBED_QUOTIENT_POSITIVE_PRIMITIVE_LC',
        new_scoped_reports=2,kernels=kernels,
        generic='For EVERY finite nonnegative globally LC sequence a with interval support starting at zero and a0>0, if its positive first difference is LC, then BOTH properties persist under EVERY uniform window [t], t>=1, and EVERY positive two-term weighted kernel c0+c1*z. NO symmetry assumption. Proof uses lower Frechet positive-part LC for two bounded nonincreasing LC inputs, the LC tail sum of old positive differences, exact mixed-window identity and BOTH joining centres.',
        quotient='For EVERY real 0<q<1, EVERY u>=0 and EVERY interval product L (no degree/count/capacity restriction), BOTH LQ_u and its positive first difference are LC, where Q_u=trunc_(<=u)(1+z)^u/(1+qz). The same holds for LQ_u(2+z) and LQ_u(1+z)^2. Q_u ULC follows the prior finite-order convolution/leading-lowering induction; lowering its final already-nonincreasing coefficient leaves all positive differences unchanged. Then apply the new generic closure per interval.',
        application='This proves the UNPERTURBED primitive LC needed for finite-padding alpha1/2 kernels. The ACTUAL alternating spectral atom is retained in the open workbench, so no actual alpha1/2 entrance follows automatically. For alpha>=3, P_alpha=[alpha+1]+z^(alpha-1) is generally not LC and is not silently treated as CI.',
        formal_scope='TWO NEW clean standard-axiom reports: complete real scalar Frechet payment; ENTIRE arbitrary-sequence clipped-LC composition including all zero cases. Written generic-window head/tail/terminal identification and Q_u ULC/primitive induction, not end-to-end actual-arm Lean formalization. Finite QA corroborates the unbounded proof and is not its substitute.',
        remaining='Actual finite-padding alpha1..h single entrance, general actual C/A2 and ORIGINAL general unamplified UI remain OPEN. No original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',QA=expected,
        state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'lc_positive_primitive_window_closure_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
