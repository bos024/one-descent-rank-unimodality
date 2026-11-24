"""Freeze ordinary binary tail induction and complete C of dominant one-jump arms."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent


def read(n):return json.loads((ROOT/n).read_text(encoding='utf8'))


def main():
    files=['binary_ordinary_tail_and_dominant_one_jump_C.tex',
        'BinaryOrdinaryTailAndOneJump.lean','BinaryOrdinaryTailAndOneJump.log',
        'audit_binary_ordinary_tail_and_one_jump_C.py','audit_binary_ordinary_tail_and_one_jump_C.json',
        'verify_binary_ordinary_tail_and_one_jump_C.py']
    log=(ROOT/'BinaryOrdinaryTailAndOneJump.log').read_text(encoding='utf8')
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==7
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    a=read('audit_binary_ordinary_tail_and_one_jump_C.json')
    assert a['status']=='PASS_EXACT_BINARY_ORDINARY_TAIL_AND_DOMINANT_ONE_JUMP_C_QA'
    assert a['counts']==dict(full_binary_ordinary_tail_minors=237248,binary_ordinary_relative_LC_minors=172137,
        ALL_nondegenerate_C_shifts=39914699,actual_dominant_one_jump_arms=5245,
        exact_mode_boundary_arms=1583,actual_binary_prefixes=1600)
    for n,status in [
        ('relative_C_inheritance_verification.json','PASS_UNBOUNDED_NORMALIZED_RELATIVE_C_INHERITANCE_AND_ONE_JUMP_REFERENCES'),
        ('binary_relative_fibonacci_C_verification.json','PASS_UNBOUNDED_BINARY_RELATIVE_FIBONACCI_AND_COMPLETE_C')]:
        dep=read(n);assert dep['status']==status
        for f,h in dep['sha256'].items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,(n,f)
        files.append(n)
    out=dict(status='PASS_UNBOUNDED_BINARY_ORDINARY_TAIL_AND_DOMINANT_ONE_JUMP_C',
        new_scoped_reports=7,kernels={'BinaryOrdinaryTailAndOneJump':7},
        ordinary_theorem='ALL alpha>=1,h>=0, FORWARD ordinary F of1alpha2^h: exactFib(n+1) throughn<=h+1, firstdefect>=1, componentwiseFib bound. ENTIREtail centresn>=h+1 LC, strict integer minor>=1 whenFn>Fprev. Full unbounded h-induction including afterordinarymodes/support/zeros. Consequently F_n/Fib(n+1) relativeLC throughFIRSTordinarymodeR whenh>=1; NOT afterR.',
        one_jump_C='ALL actual1alpha2^h L withh>=1,L>=3,L>=R=FIRSTordinarymodeofbinaryprefix have COMPLETE C, allranks/shifts. R<=2h gives simple sufficientL>=max(3,2h). NormalizedrelativeLC transfers to referenceFib(n); throughnewFIRSTDmode slopes are shifted binaryF, except exactL=R boundarycurrentM-1 improvesC. Entire count/padding/capacity family unbounded. Includes nonbinary arbitrarily many parts.',
        coupled='Existing one-armC bridge closes ALLdepth both-ordinary-rising/nonnegative-current tail nonrecovery with this family. Usual OLD head retainedforS. ENTIREproperzeroheadbothcounts>=2 with thisonejumpfamily holdsNOOLD/phasecondition via earlier Cbridge/phaseforcing.',
        formal_scope='Seven NEW ordinary-axiom scoped reports, including FULL unbounded ordinary-family tail induction and rising-prefix relativeLC implication. Actual polynomial/support/prefix/base identification and normalized-C/reference/phase application WRITTEN. Prior relativeC/reference/binary kernels reused without recounting; finite actual QA separate, not proof. No end-to-end actual-composition Lean theorem.',
        remaining='Smaller capacities3<=L<R, fullfirstmissing4 family, generalC>=6, lighterbinaryfullA2/incoming, remainingmixedc0/deeperS and ORIGINAL unamplified coefficient UI OPEN. No original least-counterexample bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'binary_ordinary_tail_and_one_jump_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
