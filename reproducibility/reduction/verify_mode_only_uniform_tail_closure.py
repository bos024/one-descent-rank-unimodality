"""Independent515-seed coverage and actual suffix-box reconstruction."""
from pathlib import Path
from itertools import combinations_with_replacement
import json,re,hashlib,sys
from verify_divided_CI_surplus_three_primitive import kernel
from verify_subdegree_CI_entrance import suffix_boxes
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_mode_only_uniform_tail_closure.json').read_text(encoding='utf8'))
    assert qa['status']=='EXACT_QA_PASS_MODE_ONLY_WINDOWS_AND_COMPLETE_SMALL_BINARY_CROSSINGS'
    assert qa['state_sha256']=='5b674c9938d077edb5f3f61f71548b4b98f6539b7c29cd3dedbf88fde06c336c'
    produced={(r['u'],tuple(r['V'])):r for r in qa['complete_minimal_crossing_seeds']}
    keys=set();integers=set();host_count=0;minor_count=0;counts={}
    for u in range(1,14):
        counts[u]=0
        for length in range(2,u//2+2):
            for V in combinations_with_replacement(range(3,u+2),length):
                h=sum(t-1 for t in V)
                if not u<h or h-(V[0]-1)>u:continue
                assert h<=2*u
                key=(u,V);keys.add(key);row=produced[key];counts[u]+=1
                assert h==row['h'] and (u+h)//2==row['padding_clamp']
                assert len(row['hosts'])==row['padding_clamp']+1
                for alpha,host in enumerate(row['hosts'],1):
                    assert host['alpha']==alpha
                    # Direct positive suffix-box sum, independent of the signed source used by primary QA.
                    F=suffix_boxes(alpha,[2]*u+list(V));W=sum(V)
                    g=[max(0,F[n]-F[n-1]) for n in range(W,len(F))];M=g.index(max(g));margins=[]
                    for n in range(1,M):
                        z=g[n]**2-g[n-1]*g[n+1];assert z>=0;integers.add(z);margins.append(z);minor_count+=1
                    assert M==host['first_tail_mode'] and margins==host['margins'];host_count+=1
    assert keys==set(produced) and len(keys)==515 and host_count==6662 and minor_count==43960
    assert {str(k):v for k,v in counts.items()}==qa['seed_counts']
    assert sorted(integers)==qa['integer_margins'] and len(integers)==24553
    source=(ROOT/'ModeOnlyCrossingCertificate.lean').read_text(encoding='utf8')
    pieces=re.findall(r'def part\d+ : List ℤ := \[([^]]*)\]',source)
    lean_rows=[int(x) for piece in pieces for x in piece.split(', ')]
    assert len(pieces)==64 and lean_rows==sorted(integers)
    if '--reconstruct-only' in sys.argv:
        print(json.dumps(dict(status='PASS_INDEPENDENT_COMPLETE_CROSSING_RECONSTRUCTION',seeds=515,actual_hosts=host_count,integer_comparisons=minor_count,distinct_margins=len(integers))),flush=True);return
    kernels={'ModeOnlyUniformWindow':kernel('ModeOnlyUniformWindow',['concave_triple_is_LC','uniform_transition_payment','signed_transition_is_nonincreasing','minimal_crossing_geometry']),
        'ModeOnlyCrossingCertificate':kernel('ModeOnlyCrossingCertificate',['all_integer_margins'])}
    files=['mode_only_uniform_tail_closure_proof.tex','ModeOnlyUniformWindow.lean','ModeOnlyUniformWindow.log',
        'ModeOnlyCrossingCertificate.lean','ModeOnlyCrossingCertificate.log','audit_mode_only_uniform_tail_closure.py',
        'audit_mode_only_uniform_tail_closure.json','emit_mode_only_crossing_certificate.py','verify_mode_only_uniform_tail_closure.py',
        'subdegree_CI_entrance_verification.json','subdegree_CI_entrance_proof.tex',
        'general_one_jump_complete_C.tex','finite_initial_ones_relative_derivative.tex',
        'binary_CI_two_seed_closure_workbench.tex','audit_binary_CI_tail_and_two_seeds.py','audit_binary_CI_tail_and_two_seeds.json']
    out=dict(status='PASS_MODE_ONLY_UNIFORM_WINDOWS_HEREDITARY_ACTUAL_TAIL_LC_AND_ALL_SMALL_BINARY_CROSSINGS',new_scoped_reports=5,kernels=kernels,
        generic='ANY nonnegative finite UI sequence with interval support and LC ONLY strictly before its FIRST mode remains UI and pre-FIRST-mode LC after convolution with EVERY uniform interval. Before old mode use truncated positive LC convolution; entire transition is concave by entering-nonincreasing/outgoing-nondecreasing values. For signed sequences nonnegative through L and nonpositive after, the positive part of EVERY uniform convolution has mode at most L and no later than the positive-only convolution, so the same pre-mode LC holds. Tail truncation preserves it. No LC of the descending positive part is needed.',
        insertion='Fix arbitrary binary u>=1 and alpha>=1. For ANY sorted CI capacity multiset V>=3 of weight W, its ACTUAL SIGNED derivative tail s_k from physical W includes its indispensable numerator unit at k0. After ANY capacity insertion t>=3 and re-sorting, the ACTUAL new signed tail from W+t is EXACTLY snew_k=sum(j=k..k+t-1)s_j. This is only a TAIL identity; early F/G and C are NOT permutation invariant. Thus pre-first-tail-mode LC of positive actual D from W is HEREDITARY under ANY CI insertion, without OLD C, ordinary F tail LC or descending D LC.',
        analytic_family='For ANY u>=1, ALL padding, actual late D is pre-first-mode LC at ALL centres N>=W+1 whenever V contains a factor L>=u+2 (one-factor analytic base from the registered general one-jump proof), OR a multifactored CI submultiset of degree u+1 (registered subdegree base), OR ANY independently verified tail-LC seed. Arbitrary other CI factors may be inserted without bound on count/degree/capacity. This asserts derivative LC, not complete C or original one-descent UI.',
        finite_principle='For EACH fixed u, to prove late D pre-mode LC for EVERY CI of degree h>u, only minimal degree-crossing seeds remain: 2<=d_i<=u,u<h<=2u,h-min d_i<=u,r<=floor(u/2)+1. Every h>u CI either has a one-factor analytic seed L>=u+2 or contains one of these deletion-minimal seeds. Padding clamp alpha<=ceil((u+h-1)/2), plus an infinite case, is analytic by symmetric-row centres. A finite entrance principle for derivative LC ONLY, not C/A2/original UI.',
        small_binary_family='PROVED every 0<=u<=13, EVERY sorted CI V>=3 with h>u, EVERY padding alpha>=1: actual positive derivative is LC at EVERY pre-first-mode centre N>=W+1. u0 is the trivial one-unit signed tail; u1 has an analytic one-factor seed; ALL remaining counts use COMPLETE515 deletion-minimal crossings,6662 actual padding hosts,43960 integer comparisons,24553 distinct kernel-checked margins. Arbitrary CI count/capacity/degree/padding is unbounded by hereditary insertion. NO corresponding tail-LC assertion when h<=u; the degree-boundary (8,12,19) counter remains valid.',
        formal_scope='FIVE NEW scoped reports: FOUR ModeOnlyUniformWindow scalar concavity/transition/signed-decrease/minimal-crossing kernels and ONE ModeOnlyCrossingCertificate ALL24553 integer margins over64 ordinary-reduction chunks (propext only). Independent capacity-multiset grammar and positive suffix-box sums rebuild ALL515 seeds/6662 hosts/43960 comparisons. Mode-only convolution, signed clipping, actual product-order tail identity, analytic one-factor base, minimal-subset coverage and padding assembly are WRITTEN, not end-to-end Lean of arbitrary compositions. Old one-jump/subdegree and LC convolution resources reused without recounting.',
        remaining='General crossing seeds at u>=14 without an analytic/hereditary seed; joining derivative LC to all own-cumulative C still needs actual early ordinary/cumulative entrance budgets. Master late-C threshold remains u>=h-1. Earlier reference C, general C/A2 and ORIGINAL general unamplified UI remain OPEN. NO original least-counterexample numerical bound upgrade.',
        general_original='OPEN',general_C='OPEN',general_A2='OPEN',actual_C_threshold='u>=h-1 UNCHANGED',
        independent_seeds=515,independent_hosts=host_count,independent_integer_comparisons=minor_count,integer_margins=24553,
        QA=qa['counts'],seed_counts=qa['seed_counts'],state_sha256=qa['state_sha256'],
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (ROOT/'mode_only_uniform_tail_closure_verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='sha256'}),flush=True)

if __name__=='__main__':main()
