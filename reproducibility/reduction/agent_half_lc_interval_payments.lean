import Mathlib

namespace AgentHalfLCIntervalPayments

-- Coefficient of [0,R]*[A,B], with all indices treated as integers.
def overlap (u R A B : ℤ) : ℤ :=
  max 0 (min B u - max A (u-R) + 1)

theorem whole_layer_and_first_point_missed
    (u v R A B : ℤ) (hAB : A ≤ B) (hB : B ≤ u)
    (hcover : u-R ≤ A) (hmiss : A+1 ≤ v-R) :
    1 ≤ overlap u R A B-overlap v R A B := by
  have hwhole : overlap u R A B=B-A+1 := by
    unfold overlap
    rw [min_eq_left hB, max_eq_left hcover]
    exact max_eq_right (by omega)
  have hright : overlap v R A B ≤ B-A := by
    unfold overlap
    apply max_le
    · omega
    · have hu := min_le_left B v
      have hl := le_max_right A (v-R)
      omega
  rw [hwhole]
  omega

theorem tail_interval_one_step_loss
    (u R A B : ℤ) (hB : B ≤ u)
    (hleft : A ≤ u-R) (hright : u-R ≤ B) :
    overlap u R A B-overlap (u+1) R A B=1 := by
  have hBnext : B ≤ u+1 := by omega
  have hleftNext : A ≤ u+1-R := by omega
  unfold overlap
  rw [min_eq_left hB, min_eq_left hBnext,
      max_eq_right hleft, max_eq_right hleftNext]
  rw [max_eq_right (show 0 ≤ B-(u-R)+1 by omega),
      max_eq_right (show 0 ≤ B-(u+1-R)+1 by omega)]
  ring

theorem late_entering_source_layer_payment
    (M s kappa r B : ℤ) (hMs : s ≤ M) (hr : 0 ≤ r)
    (hk : 2 ≤ kappa) (hpay : kappa ≤ r+3)
    (hB : r+1 ≤ B) (hbudget : r+1+B ≤ s) :
    1 ≤ overlap (M-1) (M+1-kappa) (r+1) B
       -overlap (M+r+1) (M+1-kappa) (r+1) B := by
  apply whole_layer_and_first_point_missed
  · exact hB
  · omega
  · omega
  · omega

theorem virtual_central_source_layer_payment
    (M s kappa r B : ℤ) (hk : 2 ≤ kappa)
    (hpay : kappa ≤ M-s+2*r+1)
    (hB : r+1 ≤ B) (hbudget : r+1+B ≤ s) :
    1 ≤ overlap (s-r+1) (M+1-kappa) (r+1) B
       -overlap (M+r+1) (M+1-kappa) (r+1) B := by
  apply whole_layer_and_first_point_missed
  · exact hB
  · omega
  · omega
  · omega

#print axioms whole_layer_and_first_point_missed
#print axioms tail_interval_one_step_loss
#print axioms late_entering_source_layer_payment
#print axioms virtual_central_source_layer_payment

end AgentHalfLCIntervalPayments
