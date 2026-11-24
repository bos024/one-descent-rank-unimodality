"""Emit a complete small-case scalar certificate; ordinary Lean reduction only."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_padding_three_local_prefix.json').read_text(encoding='utf8'))
    rows=qa['small_scalar_certificate'];assert len(rows)==399 and len(qa['small_contexts'])==30
    assert all(1000000*a+b*(1618033 if b>=0 else 1618034)>=0 for a,b in rows)
    text='''import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace PaddingThreeSmallCertificate

def rows : List (ℤ × ℤ) := [
'''
    text+=',\n'.join('  ('+str(a)+', '+str(b)+')' for a,b in rows)
    text+='''
]

theorem endpoint_certificate :
    rows.all (fun r => decide (0 ≤ 1000000*r.1+
      (if 0 ≤ r.2 then 1618033*r.2 else 1618034*r.2))) = true := by
  decide

theorem golden_fine_interval (p : ℝ) (hp : 1 ≤ p) (hroot : p^2=p+1) :
    1618033/1000000 < p ∧ p < 1618034/1000000 := by
  constructor
  · by_contra hn
    have h1 : 0 ≤ 1618033/1000000-p := by linarith only [hn]
    have h2 : 0 ≤ 1618033/1000000+p-1 := by linarith only [hp]
    have hprod:=mul_nonneg h1 h2
    nlinarith only [hprod,hroot]
  · by_contra hn
    have h1 : 0 ≤ p-1618034/1000000 := by linarith only [hn]
    have h2 : 0 ≤ p+1618034/1000000-1 := by linarith only [hp]
    have hprod:=mul_nonneg h1 h2
    nlinarith only [hprod,hroot]

theorem all_scalar_margins (p : ℝ)
    (hlo : 1618033/1000000 ≤ p) (hhi : p ≤ 1618034/1000000) :
    ∀ r ∈ rows, 0 ≤ (r.1:ℝ)+(r.2:ℝ)*p := by
  intro r hr
  have hend:=of_decide_eq_true (List.all_eq_true.mp endpoint_certificate r hr)
  by_cases hb : 0 ≤ r.2
  · simp only [hb, ite_true] at hend
    have hendR : (0:ℝ) ≤ 1000000*(r.1:ℝ)+1618033*(r.2:ℝ) := by exact_mod_cast hend
    have hbR : (0:ℝ) ≤ (r.2:ℝ) := by exact_mod_cast hb
    have hprod:=mul_nonneg hbR (show 0 ≤ p-1618033/1000000 by linarith only [hlo])
    nlinarith only [hendR,hprod]
  · simp only [hb, ite_false] at hend
    have hendR : (0:ℝ) ≤ 1000000*(r.1:ℝ)+1618034*(r.2:ℝ) := by exact_mod_cast hend
    have hbR : (r.2:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hb))
    have hprod:=mul_nonneg (show 0 ≤ -(r.2:ℝ) by linarith only [hbR])
      (show 0 ≤ 1618034/1000000-p by linarith only [hhi])
    nlinarith only [hendR,hprod]

#print axioms golden_fine_interval
#print axioms all_scalar_margins

end PaddingThreeSmallCertificate
'''
    (ROOT/'PaddingThreeSmallCertificate.lean').write_text(text,encoding='utf8')
    print(json.dumps(dict(complete_small_CI_contexts=30,distinct_scalar_margins=399,ordinary_Lean_reduction=True)))

if __name__=='__main__':main()
