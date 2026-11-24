"""Register only the reviewed TC induction with both complete exact finite grammars."""
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parent


def read(name):return json.loads((ROOT/name).read_text(encoding='utf8'))


def main():
    kernels=dict(TriangularSourceLargeAppend=8,TriangularSourceComplete=12,LowKappaBoundaryCertificate=1)
    files=['triangular_source_large_kappa_append.tex','triangular_source_curvature_complete.tex',
           'agent_postcount_source_mode_payment.tex','general_forward_difference_growth.tex',
           'positive_derivative_append_order.tex','first_source_multiplicity_profile.tex',
           'early_normalized_source_dyadic_profile.tex','verify_triangular_source_complete.py',
           'probe_triangular_source_induction.py','probe_triangular_source_induction.json',
           'build_low_kappa_boundary_certificate.py']
    for name,count in kernels.items():
        log=(ROOT/(name+'.log')).read_text(encoding='utf8')
        assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==count,name
        assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed']),name
        files.extend([name+'.lean',name+'.log'])
    assert '[propext]' in (ROOT/'LowKappaBoundaryCertificate.log').read_text(encoding='utf8')
    pre=read('probe_low_kappa_triangular_boundaries.json')
    pre_ind=read('verify_low_kappa_triangular_boundaries.json')
    assert pre['status']=='COMPLETE_FINITE_JET_CALCULATION' and pre['complete'] and pre['remaining_queue']==0
    assert pre_ind['status']=='PASS_COMPLETE_INDEPENDENT_LOW_KAPPA_BOUNDARY_RECONSTRUCTION'
    assert pre_ind['exact_state_set_equality'] is True
    assert pre['states']==pre_ind['counts']['independent_states']==117964
    assert pre['counts']['legal_jet_appends']==pre_ind['counts']['independent_appends']==472829
    assert pre['counts']['boundary_states']==pre_ind['counts']['independent_boundary_states']==34806
    assert pre['counts']['raw_small_budget_boundaries']==pre['counts']['excluded_by_earlier_strict_fall']==53
    assert len(pre['rejected_boundary_profiles'])==53
    assert pre['reachable_state_sha256']==pre_ind['reachable_state_sha256']
    post=read('probe_low_kappa_small_peak_TC.json')
    post_ind=read('verify_low_kappa_small_peak_TC.json')
    assert post['status']=='COMPLETE_EARLY_PEAK_FINITE_JET_CALCULATION' and post['complete'] and post['remaining_queue']==0
    assert post_ind['status']=='PASS_COMPLETE_INDEPENDENT_EARLY_PEAK_TC_JET_RECONSTRUCTION'
    assert post_ind['exact_state_set_equality'] is True
    assert post['N']==post_ind['N']==45 and post['slope_cap']==post_ind['slope_cap']==128
    assert post['states']==post_ind['counts']['independent_states']==657439
    assert post['counts']['legal_jet_appends']==post_ind['counts']['independent_appends']==10873783
    assert post['counts']['eligible_early_old_peak_appends']==post_ind['counts']['independent_eligible_appends']==484214
    assert post['counts']['necessary_guard_TC_comparisons']==post_ind['counts']['independent_necessary_guard_comparisons']==4961907
    assert post['counts']['monotone_slope_budget_prunings']==post_ind['counts']['independent_slope_prunings']==9959284
    assert post['counts'].get('unresolved_small_curvatures',0)==0 and not post['unresolved_examples']
    assert post['reachable_state_sha256']==post_ind['reachable_state_sha256']
    for stem in ['probe_low_kappa_triangular_boundaries','verify_low_kappa_triangular_boundaries',
                 'probe_low_kappa_small_peak_TC','verify_low_kappa_small_peak_TC']:
        files.extend([stem+'.py',stem+'.json'])
    files.extend(['low_kappa_boundary_states.bin','low_kappa_small_peak_states.bin'])
    out=dict(status='PASS_UNBOUNDED_TRIANGULAR_SOURCE_CURVATURE_WITH_COMPLETE_INDEPENDENT_JETS',
             triangular_source_TC='PROVED for ALL actual normalized sorted arms; kappa+3<=n<=FIRST positive-derivative mode',
             new_scoped_reports=sum(kernels.values()),kernels=kernels,
             formal_scope='21 scoped generic/kernel-decide reports. Written actual induction and exact finite grammar coverage, two independently rebuilt complete state sets; NOT end-to-end Lean verification of actual arms or enumeration.',
             pre_old_peak=dict(N=13,states=117964,appends=472829,boundaries=34806,rejected=53,
                               state_sha256=pre['reachable_state_sha256']),
             early_old_peak=dict(N=45,M_cap=128,states=657439,appends=10873783,
                                 guarded_comparisons=4961907,state_sha256=post['reachable_state_sha256']),
             unbounded_audit=['ALL legal kappa transitions and unit dents covered',
                              'Late old peak: nondecreasing universal D prefix plus FIRST mode gives M>=delta+1',
                              'Early old peak: new first mode<=old support end+1 gives whole positive tail payment and rank<=45',
                              'Slope pruning uses proved coefficientwise positive-D append monotonicity',
                              'Clipping preserves coefficients; no unproved preservation of global modes',
                              'Both finite grammars are complete; necessary mode guards are supersets'],
             exact_full_state_set_equality=True,
             general_original='OPEN',general_A2='OPEN',general_C='OPEN',
             source_overlap_remainder='Triangular single-arm budget alone does NOT pay arbitrary later two-source convolution',
             sha256={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files})
    (ROOT/'triangular_source_complete_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
