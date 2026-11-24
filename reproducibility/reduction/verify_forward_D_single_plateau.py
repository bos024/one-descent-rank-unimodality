"""Verify the strict-rising written theorem's scoped kernels and smaller exact TC certificate."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parent


def main():
    log=(ROOT/'ForwardDSinglePlateau.log').read_text(encoding='utf8')
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==4
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    qa=json.loads((ROOT/'probe_forward_derivative_single_plateau.json').read_text(encoding='utf8'))
    assert qa['status']=='FINITE_QA_ONLY_STRICT_RISING_RULE' and not qa['failures']
    p=json.loads((ROOT/'probe_low_kappa_strict_peak_TC.json').read_text(encoding='utf8'))
    v=json.loads((ROOT/'verify_low_kappa_strict_peak_TC.json').read_text(encoding='utf8'))
    assert p['status']=='COMPLETE_ALL_PEAK_STRICTNESS_FINITE_JET_CALCULATION' and p['complete'] and p['remaining_queue']==0
    assert v['status']=='PASS_COMPLETE_INDEPENDENT_STRICT_PEAK_TC_JET_RECONSTRUCTION'
    assert p['N']==v['N']==39 and p['slope_cap']==v['slope_cap']==35
    assert v['exact_state_set_equality'] is True
    assert p['states']==v['counts']['independent_states']==102630
    assert p['counts']['legal_jet_appends']==v['counts']['independent_appends']==1623669
    assert p['counts']['necessary_guard_TC_comparisons']==v['counts']['independent_necessary_guard_comparisons']==18321840
    assert p['counts'].get('unresolved_small_curvatures',0)==0 and not p['unresolved_examples']
    assert p['reachable_state_sha256']==v['reachable_state_sha256']
    files=['forward_D_single_plateau.tex','ForwardDSinglePlateau.lean','ForwardDSinglePlateau.log',
           'probe_forward_derivative_single_plateau.py','probe_forward_derivative_single_plateau.json',
           'probe_low_kappa_strict_peak_TC.py','probe_low_kappa_strict_peak_TC.json',
           'verify_low_kappa_strict_peak_TC.py','verify_low_kappa_strict_peak_TC.json',
           'low_kappa_strict_peak_states.bin','verify_forward_D_single_plateau.py']
    out=dict(status='PASS_UNBOUNDED_FORWARD_D_SINGLE_FLAT_AND_SMALLER_TC_CERTIFICATE',
             new_scoped_reports=4,
             theorem='SINGLE FORMAL arm with initial ones and later capacities>=2 in ANY order: D strictly increases through FIRST mode except possibly at finalcap+1; ell<=D_ell+2, sharp.',
             written_audit='Window of the old one-flat rising prefix strictly rises to its first mode; the sole new unit dent is finalcap+1. Actual positive-D splice retains this whole prefix. No sortedness needed for this shape result.',
             TC_alternative='ALL low-kappa peak-crossing failures require n<=39 and M<=35; complete independent exact finite grammar pays every eligible state.',
             finite_certificate=dict(N=39,M_cap=35,states=102630,appends=1623669,comparisons=18321840,
                                     exact_state_set_equality=True),
             formal_scope='Four scoped span/source/whole-height-induction/rank-region kernels. Strict-window/actual-arm induction and finite grammar coverage are written, not end-to-end Lean formalizations.',
             general_original='OPEN',general_C='OPEN',general_A2='OPEN',
             sha256={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files})
    (ROOT/'forward_D_single_plateau_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
