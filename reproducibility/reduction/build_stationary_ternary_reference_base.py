"""One fixed r=6 golden-residual tail entrance, without actual-host enumeration."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_ternary_forward_inverse import forward
from audit_arbitrary_Fibonacci_tail_late_C import sub,mul,sign
def expr(v):return f'(({v[0]+v[1]}:ℝ)+({v[1]}:ℝ)*q)'
def main():
    P=[1];C=[1]+[0]*18
    for j in range(6):
        for n,v in enumerate(P):C[n+3]+=v
        P=[0]+[sum(P[max(0,n-2):min(n+1,len(P))]) for n in range(len(P)+2)]
    H=forward(C);values=H[8:19];ms=[sub(mul(H[n],H[n]),mul(H[n-1],H[n+1])) for n in range(9,18)]
    assert all(sign(v)>0 for v in values+ms)
    props=[f'0<{expr(v)}' for v in values+ms]
    text='''import Mathlib
set_option maxHeartbeats 2000000
namespace StationaryTernaryReferenceBase
theorem exact_q_interval (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    618033988749/1000000000000 ≤ q ∧ q ≤ 618033988750/1000000000000 := by
  constructor
  · by_contra! h
    have hs := mul_self_le_mul_self hp (le_of_lt h)
    nlinarith
  · by_contra! h
    have hs := mul_self_le_mul_self (show (0:ℝ) ≤ 618033988750/1000000000000 by norm_num) (le_of_lt h)
    nlinarith
theorem complete_fixed_six_residual_tail (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    '''+' ∧\n    '.join(props)+''' := by
  have hi := exact_q_interval q hq hp
  refine ⟨'''+', '.join('?_ ' for _ in props).strip()+'''⟩ <;> nlinarith [hq,hi.1,hi.2]
#print axioms complete_fixed_six_residual_tail
end StationaryTernaryReferenceBase
'''
    (ROOT/'StationaryTernaryReferenceBase.lean').write_text(text,encoding='utf8')
    out=dict(r=6,C=C,H=H,positive_tail_values=values,LC_centres=list(range(9,18)),LC_minors=ms,exact_coverage='FULLH8..18positive/FULLHLCcentres9..17;ONEfixedbaseonly')
    (ROOT/'stationary_ternary_reference_base_data.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
