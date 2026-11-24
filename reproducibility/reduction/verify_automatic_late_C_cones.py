"""Independently identify the sole u8 residual and reconstruct its actual infinite edge."""
from pathlib import Path
from math import comb
import json,hashlib
from verify_divided_CI_surplus_three_primitive import kernel
from verify_subdegree_CI_entrance import suffix_boxes
ROOT=Path(__file__).resolve().parent

def capacity_partitions(n,lo=3):
    if n==0:yield []
    for t in range(lo,n+1):
        for rest in capacity_partitions(n-t,t):yield [t]+rest

def main():
    qa=json.loads((ROOT/'audit_automatic_late_C_cones.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_PASS_AUTOMATIC_LATE_C_CONES_AND_COMPLETE_U8_ENTRANCE'
    assert qa['state_sha256']=='ecfebb05389c38d9ab028165b50f8dadc39d4aeaf241ce4780b77088ed147ccf'
    weight=json.loads((ROOT/'multitail_binary_prefix_finite_principle_verification.json').read_text(encoding='utf8'))
    assert weight['status']=='PASS_UNBOUNDED_FIXED_MULTITAIL_FINITE_PRINCIPLE_AND_NONBINARY_WEIGHT32_COMPLETE_C'
    produced=qa['complete_u8_profiles'];independent=[]
    # Independent WEIGHT grammar, not the primary degree-partition grammar.
    for W in range(33,34):
        for V in capacity_partitions(W):
            h=W-len(V)
            if 10<=h<=22 and max(V)<=15:independent.append(V)
    assert independent==produced==[[3]*11]
    edge=qa['infinite_edge'];F=suffix_boxes(16,[2]*8+[3]*11)
    actual=[F[33]-F[32],F[34]-F[33]]
    assert actual==[edge['previous'],edge['current']]==[5109250,5076760]
    assert actual[0]-actual[1]==edge['margin']==32490
    # A THIRD reconstruction is exactly the finite double-choice expression used in Lean.
    def trinomial(n):
        return sum(comb(11,a)*comb(11-a,b) for a in range(12) for b in range(12-a) if 2*a+b==n)
    def coeff(n):
        return sum(comb(k,j)*trinomial(n-k-j) for k in range(8) for j in range(k+1) if k+j<=n)
    assert [coeff(20)+1,coeff(21)]==actual
    assert edge['alpha_infinite_representative']==16 and 8+11+16+1>34
    assert qa['integer_margins']==[32490]
    assert len(qa['complete_u8_contexts'])==16
    for row in qa['complete_u8_contexts']:
        F=suffix_boxes(row['alpha'],[2]*8+[3]*11)
        D=[0,0]+[max(0,F[n]-F[n-1]) for n in range(2,len(F))]
        assert D.index(max(D))==row['first_D_mode']<=33
        assert row['keys']==row['margins']==[] and row['upper_mode_bound']==34
    names=['improved_symmetric_row_geometry','large_interval_degree_geometry','source_body_read_before_midpoint',
        'actual_first_tail_boundary_payment','small_binary_remainder_weight32','unique_eighth_count_geometry']
    kernels={'AutomaticLateC':kernel('AutomaticLateC',names),
        'AutomaticLateCInfiniteEdge':kernel('AutomaticLateCInfiniteEdge',['certified_infinite_tail_edge'])}
    files=['automatic_late_C_cones_proof.tex','AutomaticLateC.lean','AutomaticLateC.log',
        'AutomaticLateCInfiniteEdge.lean','AutomaticLateCInfiniteEdge.log','audit_automatic_late_C_cones.py',
        'audit_automatic_late_C_cones.json','verify_automatic_late_C_cones.py',
        'multitail_binary_prefix_finite_principle_verification.json',
        'finite_initial_ones_relative_derivative.tex','subdegree_CI_entrance_verification.json',
        'subdegree_CI_entrance_proof.tex','mode_only_uniform_tail_closure_verification.json',
        'binary_CI_infinite_padding_entrance.tex','actual_all_padding_CI_entrance.tex']
    out=dict(status='PASS_UNBOUNDED_AUTOMATIC_LATE_C_CONES_AND_ALL_BINARY_COUNTS_THROUGH_EIGHT',new_scoped_reports=7,kernels=kernels,
        automatic='For EVERY ACTUAL nonempty V>=3,ANY u>=1,ALL padding: if h=sum(t-1)>=3u-1 OR maxV>=2u, the positive derivative tail from physical W=sumV is NONINCREASING, hence ALL C shifts R>=3 at EVERY N>=W+1. u0 also immediate. Improved degree cone combines the last TWO binary rows using B1=[3], lowering symmetric-row maximum centre to(3u-4+h)/2. Long-capacity cone uses degK<=h-1, leading coefficient1, exact previous numerator unit and source monotonicity through its midpoint. True source/C LR is proved for ALL m>=0; no m>=h assumption.',
        finite_principle='For EACH fixed u, combining automatic cones and registered degree-boundary C leaves ONLY u+2<=h<=3u-2,maxV<=2u-1,r<=floor(h/2),alpha<=floor((u+h)/2)+1 (last padding represents all larger paddings). Thus late C has a finite entrance for EACH binary count u. This does not assert all such finite entrances pass for all u, nor settle earlier reference C.',
        small_binary='PROVED EVERY 0<=u<=8,EVERY nonempty sorted CI tail V>=3,ALL tail counts/capacities/degrees/padding,ALL shifts R>=3,ALL current N>=W+1: ACTUAL late C. u<=7 remainder has W<=28 and uses established COMPLETE-C weight32 family. u8 remainder beyond weight32 is EXACTLY V=3^11,W33,h22; its INFINITE actual tail edge D33=5109250>D34=5076760 is fully recomputed in Lean by finite binomial/trinomial sums. Infinite positive-D UI makes its tail nonincreasing; proved same-word finite/infinite initial-ones density order then covers EVERY finite alpha. The16 finite-padding QA hosts are NOT substituted for that unbounded density proof.',
        remaining='After these results and the weight32 family, any remaining ACTUAL late C failure has u>=9,u+2<=h<=3u-2,maxV<=2u-1,W>32 (and may use its finite padding clamp). Earlier arbitrary reference C N<=W and general C/A2/ORIGINAL unamplified coefficient UI remain OPEN. First unresolved general-C count6 and original least-counterexample numerical bounds unchanged: this is LATE C only.',
        formal_scope='SEVEN NEW reports: SIX AutomaticLateC scalar degree/row/source/read/unit/weight/unique-profile kernels and ONE AutomaticLateCInfiniteEdge complete finite Nat.choose double-sum coefficient/strict-edge theorem. Standard Lean kernel reduction only, no native axiom. Independent WEIGHT partition grammar identifies the SOLE u8 residual; positive suffix-box actual F and separate trinomial/binomial calculation BOTH reconstruct D33/D34. Symmetric-row monotonicity, source LR assembly, exact actual tail formula, infinite UI, finite-initial-ones density transfer and old weight32-family application are WRITTEN, not an end-to-end Lean theorem for all compositions. Old reports reused without recounting.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',independent_u8_profiles=1,
        kernel_verified_infinite_edge=dict(previous=5109250,current=5076760,margin=32490),QA=qa['counts'],state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'automatic_late_C_cones_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
