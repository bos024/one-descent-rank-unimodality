"""Freeze the all-capacity analytic one-jump C theorem, with exact scope."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent


def read(n):return json.loads((ROOT/n).read_text(encoding='utf8'))


def main():
    files=['general_one_jump_complete_C.tex',
        'OneJumpUniformAnalyticKernels.lean','OneJumpUniformAnalyticKernels.log',
        'audit_general_one_jump_analytic_C.py','audit_general_one_jump_analytic_C.json',
        'verify_general_one_jump_analytic_C.py','ordinary_rooted_caterpillar_model.tex',
        'property_C_five_nonone_arms.tex','audit_minimum_staircase_scaled_dyadic.py']
    log=(ROOT/'OneJumpUniformAnalyticKernels.log').read_text(encoding='utf8')
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==7
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    qa=read('audit_general_one_jump_analytic_C.json')
    assert qa['status']=='PASS_EXACT_QA_UNIFORM_ANALYTIC_GENERAL_ONE_JUMP_C'
    expected=dict(exact_first_two_binary_defect_sets=3000,actual_modified_binary_tail_minors=165215,
        actual_diagonal_improved_mode_bounds=755,actual_UNIFORM_entrance_relative_LC_minors=131297,
        actual_outgoing_exact_prefix_triples=51211,actual_peak_parity_ordinary_LC_payments=19809,
        actual_valley_parity_transfers=31402,actual_rising_tail_LC_beyond_uniform_entrance=120605,
        actual_ALL_C_current_ranks=508454,actual_ALL_C_shifts_covered=61830091,
        actual_one_jump_arms=3000,actual_strict_window_lifts_inside_old_FIRST_mode=10506)
    assert qa['counts']==expected
    for n,status in [
        ('binary_ordinary_tail_and_one_jump_C_verification.json','PASS_UNBOUNDED_BINARY_ORDINARY_TAIL_AND_DOMINANT_ONE_JUMP_C'),
        ('relative_C_inheritance_verification.json','PASS_UNBOUNDED_NORMALIZED_RELATIVE_C_INHERITANCE_AND_ONE_JUMP_REFERENCES'),
        ('one_jump_fixed_capacity_finite_principle_verification.json','PASS_UNBOUNDED_FIXED_CAPACITY_FINITE_PRINCIPLE_AND_ONE_JUMP_C_THROUGH32')]:
        dep=read(n);assert dep['status']==status
        for f,h in dep['sha256'].items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,(n,f)
        files.append(n)
    out=dict(status='PASS_UNBOUNDED_ANALYTIC_COMPLETE_C_FOR_ALL_ONE_JUMP_ARMS',
        new_scoped_reports=7,kernels={'OneJumpUniformAnalyticKernels':7},
        modified_binary='ALLh>=2,n>=h+2 withordinarybinaryF_n>Fprev: (F_n-1)^2>=Fprev*(Fnext-1), hence ordinaryminor>=2F_n-Fprev-1>=Fprev+1. Exact firsttwo defects(1,h+2)/(1,h+3)/(2,2h+3), full unbounded countinduction with two distinct old-mode branches. Entire ordinary tailLC reused, not differentiated dominance.',
        valley_theorem='ANYreal normalizedincoming density(x,xu,z),0<=u<=1,z<=xu^2,p<=x<=1, outgoing densitylocalVALLEY0<=q<=p<1,q<=w<1: relativeLC survives subtractingoutgoing fromboth. Complete concavequadratic/chord and factoredendpoint proof. OppositeFibonacci parity uses modifiedinteger margin and negative referenceCassini minor.',
        uniform_entrance='ANYL>=3 andALL1<=h<=L+2,ALLalpha: actualpositiveD/r(onejump infinitebinaryreference) isrelativeLC onTRUNCATEDprefixthroughFIRSTDmode. OrdinarybinaryrelativeLC/modifiedmargin plus exactoutgoingFibtriple and paritysplit. Diagonalh=L+2 improvesell<=2h using binarysignedslope(2h)<=1 versus slope(h+2)>1. NOFINITEHOST/CAPACITYENTRANCEused.',
        full_theorem='EVERY ACTUAL1alpha2^h L,alpha>=1,h>=1,L>=3,ALLparametersUNBOUNDED,has COMPLETEpropertyC atALLpositivecurrentranks/shifts>=3. Uniformanalyticentrance replacescapacity32certificate; higherh uses FULLRISINGTAILcountinductiononlythroughFIRSTDmode, withstrictwindowliftkeepingBOTHoldreadsinsideOLD FIRSTmode. Both earlyD plusF/G ratioseeds and FINITEreadtwointegration payALLC. NoLCafteroldDmodeassumed.',
        first_weight_four_corollary='ALLactualfirstmissing4 withmaxcapacity>=4haveCOMPLETEC: count<=2oldC, count>=3exactclassificationforcesbinaryprefixplusONElastcapacity. Multiplethrees/last3firstweight4family NOTclaimed.',
        coupled='ALLdepthBOTHordinaryrising/nonnegativecurrent tailnonrecovery whenANYarmonejump orfirstweight4/max>=4, usualOLDheadretainedforS. ENTIREproperzeroheadbothcounts>=2 withthisqualifyingarm C/OLD-free withoutphasecondition bypriorbridge. Nooriginalleastcounterexampleboundupgrade.',
        formal_scope='SevenNEWordinary-axiom scopedreports, including FULLunboundedmodifiedbinaryfamilyinduction and FULLrisingreferencetailinduction, arbitraryrealvalleytheorem, exactallhboundary andparity/windowkernels. Actual word/polynomial/support/mode/reference/parityidentifications and completeunboundedCassemblyWRITTEN. EarlierLC/relativeC/reference andCseed/finite-readkernels reusedwithoutrecounting. NOFINITEcapacity32entrance orfinite-wordnonfailureusedintheNEWlogicalproof; oldcertificates remain historical independentchecks. Notend-to-endLeancompositionformalization.',
        independent_actual_QA=expected,
        remaining='GeneralnonbinaryC>=6, firstmissing4MULTIPLEthrees, fullA2/lighterbinaryincoming, remainingmixednonzerohead/deeperhigherfirstweightS, ORIGINALgeneralunamplifiedcoefficientUI OPEN. ALLonejumpCresiduals/capacitycutoffsNOWREMOVED, notoriginalUIelimination.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'general_one_jump_analytic_C_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
