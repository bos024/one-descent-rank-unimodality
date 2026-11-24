"""Independent small literal-letter QA and immutable written-dependency manifest."""
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import sys,json,hashlib
import os
S=Path(os.environ.get('ONE_DESCENT_REPLAY_DIR', Path(__file__).resolve().parent))
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R))
from verify_binary_ternary_A2_original_family import greedy_ideal,conv,UI,core

def one_arm(alpha,U):
    # Literal-letter greedy counting, not the arm recurrence or positive boxes.
    return greedy_ideal([1]*alpha+list(U))
def main():
    primary=json.loads((S/'audit_one_hereditary_C_arm_arbitrary_other.json').read_text(encoding='utf8'))
    assert primary['status']=='PASS_QA_ONE_HEREDITARY_C_ARM_ARBITRARY_OTHER_ORIGINAL'
    assert primary['formal_reports']==0 and primary['counts']['TRUE_leftmost_embedding_originals']==146
    ct=Counter();sha=hashlib.sha256()
    seeds=[(),(2,),(3,4),(2,3,4),(4,4,4),(2,4,4,4)]
    unknowns=list(combinations_with_replacement(range(4,8),6))[::11]
    for U in seeds:
      for V in unknowns:
        for exceptional in [False,True]:
            W=list(U)
            if exceptional:W.append(max(max(W or [1]),1+sum(V)-sum(W)))
            A=one_arm(2,W);B=one_arm(1,V);M=max(W+list(V)+[1])+1
            H,L,T=core(A,B,M);actual=greedy_ideal([1,1]+W+[M]+list(reversed([1]+list(V))))
            assert actual==H and all(UI(p) for p in [H,L,T])
            p=conv(A[::-1],B[::-1]);d=[max(0,x-(p[n-1] if n else 0)) for n,x in enumerate(p)]
            assert UI([x*2**n for n,x in enumerate(d)])
            ct['independent_literal_letter_ORIGINAL_and_FULL_A2']+=1
            if exceptional:ct['independent_extra_marked_heavier_appends']+=1
            sha.update(repr((U,V,W,M,actual,L,T,p)).encode())
    dependencies=['complete_mixed_source_unrestricted_C_original_criterion_proof.tex',
      'clipped_forward_ratio_frontier.tex','C_to_coupled_S_rising_window.tex',
      'coupled_source_window_A2_and_kappa_nine_original_proof.tex',
      'binary_ternary_A2_original_family_proof.tex','deficit_cumulative_ratios.tex',
      'short_prefix_reflection_join.tex','inductive_signed_window.tex',
      'audit_first_missing_twelve_original.py','verify_binary_ternary_A2_original_family.py',
      'verify_subdegree_CI_entrance.py','audit_joint_structure.py','probe_binary_first_defect_ordinary_tail.py']
    own=['one_hereditary_C_arm_arbitrary_other_original_proof.tex',
      'audit_one_hereditary_C_arm_arbitrary_other.py','audit_one_hereditary_C_arm_arbitrary_other.json',
      'verify_one_hereditary_C_arm_arbitrary_other.py']
    hashes={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in own}
    hashes.update({n:hashlib.sha256((R/n).read_bytes()).hexdigest() for n in dependencies})
    result=dict(status='PASS_UNBOUNDED_ONE_HEREDITARY_C_ARM_ARBITRARY_OTHER_ORIGINAL',
      formal_reports=0,formal_scope='ZERO new Lean reports. Previously verified weighted-sum, excess and complete mixed/window kernels; marked count induction and original relative assembly are WRITTEN.',
      theorem='For ANY final-deletion-closed actual FULL-C class C, ANY pair with at least ONE arm in C and the other COMPLETELY ARBITRARY has FULL A2 and ORIGINAL strict-core/BOTH-relative coefficient unimodality at EVERY strict peak. Unlimited legal appends to the unmarked arm; ONE extra arbitrary legal append to marked arm if its new weight is at least the other weight. No amplification or kappa bound.',
      additional='At N>=3, if current A has FULL C and eN<0, (EA EB)N<=wA(N) and eN-2eprev>=wB(N)>=0. If both have C use min(wA,wB). N=2 explicitly excluded due the low-degree correction.',
      remaining='General TWO-UNKNOWN-arm C/A2/ORIGINAL OPEN. Hereditary C cannot be replaced by uncertified current C in the induction. Finite checks are QA only.',
      independent_counts=dict(ct),independent_sha256=sha.hexdigest(),primary_sha256=primary['sha256'],sha256=hashes,
      general_C='OPEN',general_A2='OPEN',general_original='OPEN')
    (S/'one_hereditary_C_arm_arbitrary_other_verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k!='sha256'}),flush=True)
if __name__=='__main__':main()
