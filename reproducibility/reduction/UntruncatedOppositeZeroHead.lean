import Mathlib

namespace UntruncatedOppositeZeroHead

theorem low_unit_no_recovery (first current next : ℝ)
    (hf : 2 ≤ first) (hc : current < 2)
    (hshape : min first next ≤ current) : next ≤ current := by
  by_contra hn
  have hnext : current < next := by linarith
  have hfirst : current < first := by linarith
  have hm := lt_min hfirst hnext
  linarith

theorem head_pays_all_boundary_recoveries (h p1 : ℝ)
    (hh : 2 ≤ h) (hp : h+2 ≤ p1) :
    0 ≤ 2*p1-3 ∧ 1 ≤ 2*p1-3 ∧ h-1 ≤ 2*p1-3 := by
  constructor
  · linarith
  constructor <;> linarith

theorem exact_zero_head_S_margin
    (pPrev pNow pNext p1 : ℝ) :
    2*((p1-1)+(pNow-pNext))-(1+(pPrev-pNow)) =
      (2*p1-3)-((2*pNext-pNow)-(2*pNow-pPrev)) := by ring

theorem first_defect_tail_cannot_recover (s next defect : ℤ)
    (hd : 1 ≤ defect) (ht : 0 ≤ s+defect) (hs : s+defect < 2)
    (hno : s ≤ 0 → next ≤ 0) : next ≤ s+defect := by
  have hsp : s ≤ 0 := by omega
  have hn := hno hsp
  omega

#print axioms low_unit_no_recovery
#print axioms head_pays_all_boundary_recoveries
#print axioms exact_zero_head_S_margin
#print axioms first_defect_tail_cannot_recover

end UntruncatedOppositeZeroHead
