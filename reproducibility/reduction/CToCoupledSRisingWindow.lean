import Mathlib

namespace CToCoupledSRisingWindow

theorem monotone_nonnegative_excess
    (H0 H1 D0 D1 : ℝ)
    (hD1 : 0 < D1) (hH : H0 ≤ H1)
    (hratio : H0*D1 ≤ H1*D0) (hgap : D1 ≤ H1) :
    H0-D0 ≤ H1-D1 := by
  have hH1 : 0 < H1 := lt_of_lt_of_le hD1 hgap
  have hprod : 0 ≤ (H1-H0)*(H1-D1) := mul_nonneg (by linarith) (by linarith)
  have hid : H1*((H1-D1)-(H0-D0)) =
      (H1*D0-H0*D1)+(H1-H0)*(H1-D1) := by ring
  nlinarith

theorem S_from_nonrecovering_tail
    (u uNext v vNext : ℝ) (hhead : u ≤ 2*uNext)
    (htail : v ≤ 2*vNext) : u+v ≤ 2*(uNext+vNext) := by linarith

theorem two_defects_force_two_positive_slopes
    (HA HB excess DA DB : ℤ) (hA : 2 ≤ HA) (hB : 2 ≤ HB)
    (he : 0 ≤ excess) (hel : excess < 2)
    (hDA : DA=HA-excess) (hDB : DB=HB-excess) :
    1 ≤ DA ∧ 1 ≤ DB := by omega

#print axioms monotone_nonnegative_excess
#print axioms S_from_nonrecovering_tail
#print axioms two_defects_force_two_positive_slopes

end CToCoupledSRisingWindow
