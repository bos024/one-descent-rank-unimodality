"""Register the reviewed unbounded source-notch induction and actual obstruction."""
from pathlib import Path
import json,hashlib

ROOT=Path(__file__).resolve().parent


def read(name):return json.loads((ROOT/name).read_text(encoding='utf8'))


def main():
    stem='SourceCurvatureSingleNotch'
    log=(ROOT/(stem+'.log')).read_text(encoding='utf8')
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==7
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    assert "exact_actual_counterexample_member' depends on axioms: [propext]" in log
    qa=read('probe_source_single_notch.json')
    assert qa['status']=='PASS_FINITE_QA_SINGLE_NOTCH_AND_SHARP_LATE_MONOTONICITY_OBSTRUCTION'
    assert qa['counts']['complete_N47_nonrect_prefix_states']==207002
    assert qa['counts']['notch_edges']==5229289
    assert qa['counts']['unbounded_obstruction_family_instances']==4500
    second=read('probe_second_overlap_all_multiplicities.json')
    assert second['status']=='FINITE_FULL_SECOND_OVERLAP_NONFAILURE_ONLY' and second['witness'] is None
    assert second['counts']=={'actual_pairs':120000,'both_primitives_strictly_rising':89181}
    assert second['kappa_three_jets']==[[1,1]]
    dependencies={
        'triangular_source_complete_verification.json':'PASS_UNBOUNDED_TRIANGULAR_SOURCE_CURVATURE_WITH_COMPLETE_INDEPENDENT_JETS',
        'forward_D_single_plateau_verification.json':'PASS_UNBOUNDED_FORWARD_D_SINGLE_FLAT_AND_SMALLER_TC_CERTIFICATE',
        'joint_source_growth_verification.json':'PASS_UNBOUNDED_JOINT_AND_OFFSET_LINEAR_SOURCE_CURVATURE'}
    for name,status in dependencies.items():
        out=read(name);assert out['status']==status
        for path,expected in out['sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,(name,path)
    files=['source_curvature_single_notch.tex',stem+'.lean',stem+'.log','probe_source_single_notch.py',
           'probe_source_single_notch.json','verify_source_single_notch.py',
           'probe_second_overlap_all_multiplicities.py','probe_second_overlap_all_multiplicities.json']+list(dependencies)
    out=dict(status='PASS_UNBOUNDED_SOURCE_SINGLE_NOTCH_AND_IMMEDIATE_RECOVERY',new_scoped_reports=7,
             theorem='ALL actual nonrectangular SORTED arms: source increment w_n is nondecreasing at 3<=n<=FIRSTDmode except possibly n=lastcap+2. If lastcap+3<=FIRSTDmode, w_(lastcap+3)>=w_(lastcap+1).',
             corollaries=['EVERY rank >=lastcap+3 through FIRSTDmode dominates ALL earlier source increments',
                          'ALL sorted-legal capacity windows compare source increments whenever both indices are before FIRSTDmode',
                          'More generally strict entering D>leaving D implies entering source w>=leaving source w, including peak-crossing windows'],
             obstruction='Unbounded ACTUAL 1^alpha(2,T,T+1), T>=6, alpha>=T: kappa5/delta2/eta6, FIRSTDmode=T+3, height2T-1, curvature at T+2/T+3 is 2T-2/2T-3. Thus strict late monotonicity is FALSE at arbitrarily large offsets with FIXED kappa5.',
             proof_audit=['Simultaneous induction of single-notch monotonicity and two-edge recovery',
                          'Strict old entering-vs-leaving D survives the one possible NEW flat at t+1',
                          'Before old mode, old recovery gives the required spaced source order',
                          'Across old mode, w_enter>=D_enter>D_leave>=w_leave',
                          'Only negative isolated second-source term is at NEW t+2',
                          'Recovery sum is w_old(t+1)+w_old(t+2)-1; birth or proved offset2/TC positivity pays it',
                          'No generic coefficient dominance is differentiated; no original/general C/A2 claim'],
             formal_scope='7 scoped kernel reports, including unbounded finite-chain record and whole crossing-window comparison, plus kernel-decide actual member 1^6(2,6,7). Actual-arm induction and unbounded family polynomial identifications written, NOT end-to-end Lean formalized.',
             logical_dependencies='TC, one-flat forward D, and the complete offset-two lemma. The larger J theorem and N47 peak enumeration are not needed for the written induction; their report supplies the independently verified offset lemma and extra finite QA.',
             second_overlap='COMPLETE BOTH-ORDINARY-FORWARD-RISING branch when EITHER first weight is THREE: eligible kappa3 arm has delta=eta=1; the other J budget pays the entire second-overlap product. ALL-head S in that branch with usual OLD head; ENTIRE zero-head second overlap for counts>=2 without C/OLD A2 because its slopes are forced positive. Separate written exact-generation classification, not inferred from finite QA. No general mixed-branch conclusion.',
             finite_QA=qa['counts'],general_original='OPEN',general_C='OPEN',general_A2='OPEN',
             sha256={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files})
    (ROOT/'source_single_notch_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
