"""Frozen complete certificate + written unbounded assembly + actual-model QA."""
from pathlib import Path
import json,hashlib,time
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
def main():
    start=time.monotonic()
    cert=json.loads((ROOT/'first_missing_twelve_head_certificate_verification.json').read_text(encoding='utf8'))
    assert cert['status']=='PASS_INDEPENDENT_COMPLETE_FIRST_MISSING_TEN_THROUGH_TWELVE_SOURCE_OR_HEAD_CERTIFICATE'
    for n,digest in cert['sha256'].items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==digest,n
    assert cert['counts']['complete_rank_states']==3241
    assert cert['counts']['complete_owner_rank_inputs']==1858242
    assert cert['counts']['positive_curvature_owner_edges']==72043
    assert cert['kernel_obligations']==75372 and cert['chunks']==754 and cert['modules']==31
    assert sum(len(x) for x in cert['kernels'].values())==5
    qa=json.loads((ROOT/'audit_first_missing_twelve_original.json').read_text(encoding='utf8'))
    assert qa['status']=='PASS_QA_FIRST_MISSING_TWELVE_CLOSED_SOURCE_WINDOWS_AND_A18_ORIGINAL'
    assert qa['counts']['TRUE_greedy_original_rank_counts']==360222
    deps=['coupled_source_kappa_nine_verification.json',
      'coupled_source_window_A2_and_kappa_nine_original_proof.tex',
      'CoupledSourceWindowA2.lean','CoupledSourceWindowA2.log',
      'uniform_gap_eight_six_part_owner.tex',
      'probe_gap_eight_hsix_source_complement.py','probe_gap_eight_hsix_source_complement.json',
      'verify_gap_eight_hsix_source_complement.py','verify_gap_eight_hsix_source_complement.json',
      'source_birth_gap_nonrecovery.tex','source_birth_gap_refinements.tex',
      'arbitrary_source_gap_finite_owner.tex','source_curvature_linear_owner.tex',
      'kappa_nine_source_nonrecovery.tex','mixed_head_raw_primitive_LC.tex',
      'agent_mixed_strict_head_74.tex','agent_mixed_strict_head_74_verification.json',
      'complete_capacity_four_verification.json','complete_capacity_four_C_original_proof.tex',
      'relative_golden_head_dominant_C_verification.json','relative_golden_head_dominant_C_proof.tex',
      'multitail_binary_prefix_finite_principle_verification.json','multitail_binary_prefix_finite_principle.tex',
      'binary_ternary_A2_original_family_verification.json','binary_ternary_A2_original_family_proof.tex',
      'C_to_coupled_S_rising_window.tex','agent_bothdeclining_first_birth.tex',
      'agent_half_lc_actual_weak_curvature.tex','inductive_signed_window.tex',
      'short_prefix_reflection_join.tex','verify_binary_ternary_A2_original_family.py',
      'audit_joint_structure.py','probe_binary_first_defect_ordinary_tail.py']
    for name in [x for x in deps if x.endswith('_verification.json')]:
        dep=json.loads((SOURCE/name).read_text(encoding='utf8'))
        for n,d in dep.get('sha256',{}).items():assert hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()==d,(name,n)
    local=list(cert['sha256'])+['first_missing_twelve_head_certificate_verification.json',
      'first_missing_twelve_original_criterion_proof.tex','audit_first_missing_twelve_original.py',
      'audit_first_missing_twelve_original.json','verify_first_missing_twelve_original_criterion.py']
    out=dict(status='PASS_FIRST_MISSING_TWELVE_FULL_C_TO_A2_ORIGINAL_A18_CRITERION',new_scoped_reports=5,
      kernels=cert['kernels'],
      criterion='ANYfinaldeletionclosedACTUALFULLCclass/kappa<=12=>FULLpairA2/ORIGINALstrictCORE+BOTHrelativesANYstrictpeak+ONEarbitrarylegalheavierappend. NOamplification. FrozencompleteCLOSED-gapS-to-FULLwindowA2bridgeassembledwithNEWcompleteK10..12source-or-headcoverage.',
      complete_certificate='ALL3241rankstates:859headpaid/1983rational-sourcepaid/399completeowner-complementlayers. ALL1858242owner-rankinputs/1786199noncritical/72043positiveALLdirectsourcepaid;945847distinctownerssummedoverK. ALL75372explicitkernelobligations:3266rationalintegers+63headpairs+72043actualsourceSUMinequalities. 754chunks/31memory-boundedmodules/ONEpublicaggregate. IndependentTOTAL-degree/MAXIMUM-partgrammar,PRODUCT-fractions,POSITIVEsuffix-box/binomialbinaryseedpolynomials reconstructEVERYstate/category/operand/layerhash/criticalstream/publicproof.',
      strict_head='ANYnewK10..12positiveQrecovery=>j-2<=S_K(18,23,28). Negative-rbirthmiss=>j<=K-2. ProperBOTHwindows=>k+1<=j-2and<=a-1. GenuineoppositemainCIdegree37/46/56,otherdegree29/37/46=>ACTUALsignedDeltaqY>=1throughS_K. ONEraw-headconvolutiontermpaysr<k;frozenRAWrelative+1surpluspaysr>=kwithCLOSEDsourcegapincludingEQUALITY. NoRAWwindowUIclaim.',
      original_A18='A18=A15 UNIONALLmax4prefixFIVE,SIX,SEVENsuccessivedominantcapacitiesT_i>=2(W0+sumpreviousT),T1>=max5,2W0 UNIONmaxcap11/nonbinaryweight<=32arms. ALLuniformFULLC/kappa<=12/finaldeletionclosed. BOTHarmsSEVENindependentdominantjumps/ANYstrictpeak+ONEextraarbitrarylegalheavierappend. COREandBOTHrelativecoefficientsUI.',
      formal_scope='FIVEnewstandardaxiomreports:FOURunboundedowner/head/birthguards+ONEcompleteALL75372-obligationaggregate. It imports31fullykernel-compiledparts;everycritical source SUM operand is explicit and independently matched. Finitegrammar/noncriticalcurvaturedecisionsindependentlyexact,NOTendtoendLeanwords. ActualCI/source/gap/closed-S-window/A1/A2/originalassemblyWRITTENusingfrozeninputs. Additionalactualwindow/truegreedychecksQAONLY.',
      general_original='OPEN',general_C='OPEN',general_A2='OPEN',
      finite_proof_counts=cert['counts'],finite_state_sha256=cert['ALL_owner_state_sha256'],
      critical_stream_sha256=cert['critical_stream_sha256'],actual_QA=qa['counts'],
      local_files=local,dependency_files=deps,
      sha256={n:hashlib.sha256(((ROOT if n in local else SOURCE)/n).read_bytes()).hexdigest() for n in local+deps},
      seconds=time.monotonic()-start)
    (ROOT/'first_missing_twelve_original_criterion_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['kernels','sha256','local_files','dependency_files']}),flush=True)
if __name__=='__main__':main()
