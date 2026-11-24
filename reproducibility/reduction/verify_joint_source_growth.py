"""Verify scope and exact certificates for the written J and L inductions."""
from pathlib import Path
import hashlib,json,struct

ROOT=Path(__file__).resolve().parent


def read(name):return json.loads((ROOT/name).read_text(encoding='utf8'))


def main():
    kernels={'JointSourceGrowth':9,'SecondOffsetSourceCertificate':1}
    files=['joint_source_growth_complete.tex','verify_joint_source_growth.py',
           'build_second_offset_source_certificate.py','second_offset_source_certificate_build.json',
           'probe_low_kappa_joint_source.py','probe_low_kappa_joint_source.json',
           'verify_low_kappa_joint_source.py','verify_low_kappa_joint_source.json',
           'low_kappa_joint_source_states.bin']
    for name,count in kernels.items():
        log=(ROOT/(name+'.log')).read_text(encoding='utf8')
        assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==count,name
        assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed']),name
        files.extend([name+'.lean',name+'.log'])
    assert '[propext]' in (ROOT/'SecondOffsetSourceCertificate.log').read_text(encoding='utf8')
    small=read('second_offset_source_certificate_build.json')
    assert (small['N'],small['states'],small['retained_edges'],small['excluded_small_curvature_states'])==(6,106,179,15)
    assert small['exact_projection_from_independent_13_jet_state_set']
    assert hashlib.sha256((ROOT/'SecondOffsetSourceCertificate.lean').read_bytes()).hexdigest()==small['lean_sha256']
    large=read('probe_low_kappa_joint_source.json');ind=read('verify_low_kappa_joint_source.json')
    assert large['status']=='COMPLETE_JOINT_SOURCE_PEAK_FINITE_JET_CALCULATION'
    assert large['complete'] and large['remaining_queue']==0 and not large['unresolved_examples']
    assert (large['N'],large['old_kappa_max'],large['slope_cap'],large['states'])==(47,7,43,207049)
    assert ind['status']=='PASS_COMPLETE_INDEPENDENT_JOINT_SOURCE_PEAK_JET_RECONSTRUCTION'
    assert ind['exact_state_set_equality'] and ind['N']==47 and ind['slope_cap']==43
    mapping={'independent_states':'expanded_states','independent_appends':'legal_jet_appends',
             'independent_eligible_appends':'eligible_all_old_peak_appends',
             'independent_necessary_guard_comparisons':'necessary_guard_TC_comparisons',
             'independent_slope_prunings':'monotone_slope_budget_prunings'}
    for a,b in mapping.items():assert ind['counts'][a]==large['counts'][b]
    assert large['counts']['necessary_guard_TC_comparisons']==53508829
    raw=(ROOT/'low_kappa_joint_source_states.bin').read_bytes()
    assert len(raw)==207049*98
    assert hashlib.sha256(raw).hexdigest()==large['reachable_state_sha256']==ind['reachable_state_sha256']
    # Additional QA on every certified old prefix. The induction and clamping
    # proof, rather than finite nonfailure, establish J and L unboundedly.
    jet_counts={'linear':0,'joint':0,'offset_two':0}
    fmt=struct.Struct('<'+'H'*48)
    for start in range(0,len(raw),98):
        p=fmt.unpack_from(raw,start);kap=raw[start+97]
        if kap<3:continue
        d=[0,0]+[max(0,p[i]-p[i-1]) for i in range(2,48)]
        m=d.index(max(d));delta=2*p[kap-1]-p[kap];eta=2*p[kap]-p[kap+1]
        if kap+2<=m:
            assert 3*p[kap+1]-p[kap+2]-2*p[kap]>=1
            jet_counts['offset_two']+=1
        for n in range(kap+3,m+1):
            w=3*p[n-1]-p[n]-2*p[n-2]
            assert w>=n-kap-2
            jet_counts['linear']+=1
            if n>=kap+4:
                assert w>=delta+eta
                jet_counts['joint']+=1
    dependencies={'triangular_source_complete_verification.json':
                  'PASS_UNBOUNDED_TRIANGULAR_SOURCE_CURVATURE_WITH_COMPLETE_INDEPENDENT_JETS',
                  'forward_D_single_plateau_verification.json':
                  'PASS_UNBOUNDED_FORWARD_D_SINGLE_FLAT_AND_SMALLER_TC_CERTIFICATE'}
    for name,status in dependencies.items():
        dep=read(name);assert dep['status']==status
        for path,expected in dep['sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,(name,path)
        files.append(name)
    files+=['source_birth_gap_refinements.tex','agent_bothrising_source_envelope.tex',
            'early_normalized_source_dyadic_profile.tex']
    out=dict(status='PASS_UNBOUNDED_JOINT_AND_OFFSET_LINEAR_SOURCE_CURVATURE',
             new_scoped_reports=10,kernels=kernels,
             joint_J='ALL actual nonrectangular sorted arms: DeltaE_n>=delta+eta for kappa+4<=n<=FIRSTDmode',
             offset_linear_L='ALL actual nonrectangular sorted arms: DeltaE_n>=n-kappa-2 for kappa+3<=n<=FIRSTDmode',
             offset_two='ALL actual sorted arms with FIRSTDmode>=kappa+2: DeltaE_(kappa+2)>=1',
             second_overlap='ALL multiplicities ONE on BOTH arms; joint budgets pay full second-overlap convolution when both D rise. Usual OLD-head premise retained for S.',
             complete_small_certificate=dict(N=6,states=106,edges=179,rejected=15,ALL_closure_kernel_checked=True),
             complete_peak_certificate=dict(N=47,M_cap=43,states=207049,appends=3905898,
                                            comparisons=53508829,exact_state_set_equality=True),
             whole_certified_prefix_QA=jet_counts,
             proof_audit=['Strong induction on actual sorted non-one count; one-capacity base has empty range',
                          'ALL three source phases; exact second jet and both isolated units retained',
                          'Pre-peak J uses OLD J, proved TC, and complete offset-two positivity',
                          'Peak crossing uses full positive tail and sharp ell<=M+2',
                          'ALL old kappa>=8 paid by unbounded exponential-quadratic inequality',
                          'ALL old kappa<=7 failures n<=47/M<=43, complete independently rebuilt exact grammar',
                          'Monotone-D pruning is preserved on every actual ancestor; no global mode clamping claim',
                          'L has its own complete pre-peak window and unconditional peak proof'],
             formal_scope='9 scoped finite-window/scalar reports plus 1 complete N6 base-and-closure-and-curvature kernel certificate. Actual-arm identifications, induction and N47 coverage written; large enumeration independently exact, NOT kernel/end-to-end Lean formalized.',
             general_original='OPEN',general_C='OPEN',general_A2='OPEN',
             remaining='Higher-multiplicity second overlap, arbitrary later overlap, remaining mixed c0 and short-prefix incoming reads are OPEN.',
             sha256={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files})
    (ROOT/'joint_source_growth_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
