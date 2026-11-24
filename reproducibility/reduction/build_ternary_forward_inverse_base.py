"""Emit ONE explicit thirteen-coefficient base identity, no parameter enumeration."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from probe_ternary_forward_inverse import kernel,forward
from audit_arbitrary_Fibonacci_tail_late_C import add,sub,mul,sign,power

def expr(x):
    a,b=x
    return f'(({a+b}:ℝ)+({b}:ℝ)*q)'
def main():
    E=kernel(0,6);f=forward(E);tau=f[-1]
    assert tau==power((4,-2),6)
    margins=[sub(mul(f[i],f[i]),mul(f[i-1],f[i+1])) for i in range(1,len(f)-1)]
    potential=sub((1,1),mul((-12,14),tau))
    assert all(sign(a)>0 for a in f+margins+[potential])
    props=[f'0 < {expr(a)}' for a in f]
    props += [f'{expr(f[i-1])}*{expr(f[i+1])} ≤ {expr(f[i])}^2' for i in range(1,len(f)-1)]
    props += [f'2*(1+q+6*q)*{expr(tau)} ≤ (1+q)^2']
    text='''import Mathlib
set_option maxHeartbeats 2000000
namespace TernaryForwardInverseBase
theorem exact_pure_three_six_base (q : ℝ) (hq : q^2+q=1)
    (hlo : 618033988/1000000000 ≤ q) (hhi : q ≤ 618033989/1000000000) :
    '''+' ∧\n+    '.replace('+','').join(props)+''' := by
  refine ⟨'''+', '.join('?_ ' for _ in props).strip()+'''⟩ <;> nlinarith [hq]
#print axioms exact_pure_three_six_base
end TernaryForwardInverseBase
'''
    (ROOT/'TernaryForwardInverseBase.lean').write_text(text,encoding='utf8')
    data=dict(E=E,forward=f,margins=margins,potential_margin=potential)
    (ROOT/'ternary_forward_inverse_base_data.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data))
if __name__=='__main__':main()
