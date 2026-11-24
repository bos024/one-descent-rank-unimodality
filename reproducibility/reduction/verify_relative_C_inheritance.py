"""Register the unbounded written inheritance and one-jump reference results."""
from pathlib import Path
import json,hashlib

ROOT=Path(__file__).resolve().parent


def main():
    files=['relative_C_inheritance_and_one_jump_reference.tex',
        'audit_relative_C_and_one_jump_reference.py','audit_relative_C_and_one_jump_reference.json',
        'verify_relative_C_inheritance.py']
    kernels={'RelativeCClosure':7,'OneJumpReferenceC':7}
    for stem,count in kernels.items():
        log=(ROOT/(stem+'.log')).read_text(encoding='utf8')
        assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==count
        assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
        files += [stem+'.lean',stem+'.log']
    a=json.loads((ROOT/'audit_relative_C_and_one_jump_reference.json').read_text(encoding='utf8'))
    assert a['status']=='PASS_EXACT_QA_RELATIVE_C_AND_ONE_JUMP_REFERENCE' and a['counter'] is None
    assert a['counts']==dict(reference_LC_minors=12232,reference_all_shift_C=844008,
        one_jump_tilt_C=303072,one_jump_relative_density_C=178112,
        abstract_reference_C=105000,abstract_tilt_C=315000,
        exact_tilt_kernel_identities=30000,abstract_relative_density_C=105000)
    out=dict(status='PASS_UNBOUNDED_NORMALIZED_RELATIVE_C_INHERITANCE_AND_ONE_JUMP_REFERENCES',
        kernels=kernels,new_scoped_reports=14,
        inheritance='ANY nonnegative reference slopes r2=1 with property C at a current rank for EVERY shift>=3: normalized geometric tilting a^(n-2),0<a<=1 preserves C. Full C passes to EVERY normalized nonincreasing relatively log-concave density. Exact positive-kernel identity includes preserved rank-zero atom correction; low/high threshold alternatives cover all parameters/ranks.',
        read_prefix_refinement='For k=N-R, either universal k*DN<=(k+1)*Dprev pays C, or only current a<=1 and density ratio order on ranks3..k are needed. No relative-LC/order hypothesis at unread ranks k+1..N-1. This is a sufficient criterion, not a proved all-actual invariant.',
        reference='EVERY L>=3, infinite binary H2=1/(1-z-z^2) followed by capacityL: rN=FibN-Fib(N-L), positive cumulative g is LC and has complete C at EVERY rank/shift. Constant-shift Fibonacci Cassini amplitude CL=LucasL-1-(-1)^L paid by (L-1)*FibL. ALL normalized geometric tilts and relative-LC descendants inherit C.',
        formal_scope='14 NEW scoped Lean kernels: rational tilt identity/positive kernel/universal cumulative ratio/two-branch payment/density comparison; Cassini recurrence/constant-shift minors/amplitude/endpoint payments. Entire sequence-level formal-series/LR/Fibonacci assembly is the accompanying unbounded WRITTEN proof, not end-to-end Lean. Exact finite QA is independent corroboration only, not finite extrapolation.',
        remaining='Actual finite binary-prefix+ONE-jump relative-LC bridge not proved. General multi-tail reference and actual read-prefix order not proved. General nonbinaryC>=6, general A2, ORIGINAL unamplified coefficient UI remain OPEN; no original least-counterexample count upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'relative_C_inheritance_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
