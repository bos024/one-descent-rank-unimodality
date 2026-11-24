"""Freeze unbounded fixed-capacity finite principle and complete 3..32 family."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent


def read(n):return json.loads((ROOT/n).read_text(encoding='utf8'))


def main():
    files=['one_jump_fixed_capacity_finite_principle.tex',
        'OneJumpFixedCapacityClosure.lean','OneJumpFixedCapacityClosure.log',
        'build_one_jump_fixed_capacity_C_entrance.py','one_jump_fixed_capacity_C_entrance.json',
        'verify_one_jump_fixed_capacity_C_entrance.py','one_jump_fixed_capacity_C_entrance_verification.json',
        'audit_one_jump_fixed_capacity_propagation.py','audit_one_jump_fixed_capacity_propagation.json',
        'audit_minimum_staircase_scaled_dyadic.py','verify_one_jump_fixed_capacity_finite_principle.py']
    log=(ROOT/'OneJumpFixedCapacityClosure.log').read_text(encoding='utf8')
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==5
    assert not any(s in log for s in ['error:','warning:','sorryAx','ofReduceBool','failed'])
    p=read('one_jump_fixed_capacity_C_entrance.json')
    i=read('one_jump_fixed_capacity_C_entrance_verification.json')
    assert p['status']=='COMPLETE_FIXED_CAPACITY_ONE_JUMP_C_ENTRANCE'
    assert i['status']=='PASS_INDEPENDENT_COMPLETE_FIXED_CAPACITY_ONE_JUMP_C_ENTRANCE'
    assert i['producer_sha256']==hashlib.sha256((ROOT/'one_jump_fixed_capacity_C_entrance.json').read_bytes()).hexdigest()
    assert p['max_capacity']==i['max_capacity']==32
    expected=dict(ALL_actual_entrance_words=19605,ALL_current_ranks_envelope_checked=791451,
        ALL_shift_comparisons_covered=20029138,ALL_full_tail_base_minors=36427,
        ALL_full_tail_base_padding_classes=1110)
    assert p['counts']==i['counts']==expected
    assert [r['L'] for r in p['rows']]==list(range(3,33))
    assert [r['L'] for r in i['rows']]==list(range(3,33))
    for a,b in zip(p['rows'],i['rows']):
        assert a['H']==b['H']==a['L']+2
        assert a['counts']==b['counts'] and a['all_actual_prefix_sha256']==b['all_actual_prefix_sha256']
        assert a['minimum_C_envelope_slack']>=0 and a['minimum_LC_base_minor']>=0
    qa=read('audit_one_jump_fixed_capacity_propagation.json')
    assert qa['status']=='PASS_EXACT_ONE_JUMP_FIXED_CAPACITY_UNBOUNDED_PROPAGATION_QA'
    assert qa['counts']==dict(actual_FULL_tail_minors_beyond_entrance=118938,
        actual_complete_first_defect_seed_sets=1000,actual_C_current_ranks_beyond_entrance=226220,
        actual_C_shifts_covered_beyond_entrance=31126515,actual_signed_h_recursion_tail_edges=125858,
        actual_profiles_beyond_entrance=1000)
    depn='binary_ordinary_tail_and_one_jump_C_verification.json';dep=read(depn)
    assert dep['status']=='PASS_UNBOUNDED_BINARY_ORDINARY_TAIL_AND_DOMINANT_ONE_JUMP_C'
    for f,h in dep['sha256'].items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,(depn,f)
    files.append(depn)
    out=dict(status='PASS_UNBOUNDED_FIXED_CAPACITY_FINITE_PRINCIPLE_AND_ONE_JUMP_C_THROUGH32',
        new_scoped_reports=5,kernels={'OneJumpFixedCapacityClosure':5},
        finite_principle='ANY fixedL>=3,H=L+2: completeC for ALL1<=h<=H,1<=alpha<=h+L plus FULLpositiveDtailLC baseh=H suffice for COMPLETEC ofALLactual1alpha2^h L atALLh/alpha/ranks/shifts. EntirepositiveDsupport<=2h+L, paddingalpha clamps toh+L throughread2h+L+1 by exactbinaryboundary. Whole-tail signed two-term/terminaltrim induction, reference Cassini amplitude paidbyrh>=CL, TWO early D-ratio seeds plusF/G seeds, finite-prefix two-integration propagation. No guessed word-count cutoff.',
        completed_family='ALL actual1alpha2^h L,alpha/hUNBOUNDED,3<=L<=32 have COMPLETEC. Combined dominantL>=R theorem proves COMPLETEC forALLh<=16 atARBITRARYL>=3. EntireonejumpC residualrequires h>=17,L>=33,L<R<=2h. This restriction is AUXILIARY, NOToriginalleastcounterexampleupgrade.',
        complete_independent_entrance=expected,
        coupled='Prior one-armC bridges apply: ALLdepth BOTHordinaryrising/nonnegativecurrent tailnonrecovery with usualOLDheadforS; ENTIREproperzeroheadbothcounts>=2 C/OLD-free withoutphasecondition. Remainingmixed/deeper/incoming notinferred.',
        formal_scope='FiveNEW ordinary-axiom scoped reports: FULL genericreference/terminaltrim tailinduction, amplitudebudget, BOTHfirstdefectseedratios, FULL FINITE-read two-integration propagation, paddinggeometry. Actual word/reference/positive-support/finitecoverage/C assembly WRITTEN. ALL19605 actual entrancewords/20029138 literal shifts/36427baseLCminors independently rebuilt by closedbinomial/directwindow/integratedD, NOproducerimplementation import. Entrance notend-to-endLean; finiteQA separate, no arbitraryL completion.',
        remaining='GeneralonejumpL>=33 withh>=17 andL<R, generalC>=6, fullA2/lighterbinaryincoming, mixedc0/deeperS and ORIGINAL unamplified coefficient UI OPEN. Full firstmissing4 family notclosed; nooriginalleastcounterexampleboundupgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'one_jump_fixed_capacity_finite_principle_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)


if __name__=='__main__':main()
