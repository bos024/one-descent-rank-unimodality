import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace TribonacciInverseClosure

theorem cubic_monotone (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    a^3-a^2-a-1 ≤ b^3-b^2-b-1 := by
  have hb : 1 ≤ b := ha.trans hab
  have h1 := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ b-1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ a-1 by linarith)
  have h3 : 0 ≤ a*b-1 := by nlinarith
  have hp := mul_nonneg (show 0 ≤ b-a by linarith)
    (show 0 ≤ b^2+a*b+a^2-a-b-1 by nlinarith)
  nlinarith

theorem root_interval_from_cubic_endpoint_signs (x L U : ℝ)
    (hx : 1 ≤ x) (_hL : 1 ≤ L) (hU : 1 ≤ U)
    (hroot : x^3-x^2-x-1=0)
    (hl : L^3-L^2-L-1 < 0) (hu : 0 < U^3-U^2-U-1) :
    L ≤ x ∧ x ≤ U := by
  constructor
  · by_contra! h
    have hm := cubic_monotone x L hx (le_of_lt h)
    linarith
  · by_contra! h
    have hm := cubic_monotone U x hU (le_of_lt h)
    linarith

theorem quadratic_interval_lower_bound (x L U A B C : ℝ)
    (hL : 0 ≤ L) (hlo : L ≤ x) (hhi : x ≤ U) :
    A+(if 0 ≤ B then B*L else B*U)
      +(if 0 ≤ C then C*L^2 else C*U^2) ≤ A+B*x+C*x^2 := by
  have hx : 0 ≤ x := hL.trans hlo
  have hL2 : L^2 ≤ x^2 := by nlinarith [mul_self_le_mul_self hL hlo]
  have hU2 : x^2 ≤ U^2 := by nlinarith [mul_self_le_mul_self hx hhi]
  have hB : (if 0 ≤ B then B*L else B*U) ≤ B*x := by
    by_cases h : 0 ≤ B
    · simp only [ite_eq_left h];exact mul_le_mul_of_nonneg_left hlo h
    · simp only [ite_eq_right h];exact mul_le_mul_of_nonpos_left hhi (le_of_lt (lt_of_not_ge h))
  have hC : (if 0 ≤ C then C*L^2 else C*U^2) ≤ C*x^2 := by
    by_cases h : 0 ≤ C
    · simp only [ite_eq_left h];exact mul_le_mul_of_nonneg_left hL2 h
    · simp only [ite_eq_right h];exact mul_le_mul_of_nonpos_left hU2 (le_of_lt (lt_of_not_ge h))
  linarith

theorem strict_finite_Bernstein_combination {ι : Type*} (s : Finset ι)
    (c b : ι → ℝ) (hc : ∀ i ∈ s,0 < c i) (hb : ∀ i ∈ s,0 ≤ b i)
    (hunit : ∑ i ∈ s,b i=1) : 0 < ∑ i ∈ s,c i*b i := by
  have hs : 0 < ∑ i ∈ s,b i := by rw [hunit];norm_num
  obtain ⟨i,hi,hbi⟩ := (Finset.sum_pos_iff_of_nonneg hb).mp hs
  exact Finset.sum_pos' (fun j hj => mul_nonneg (le_of_lt (hc j hj)) (hb j hj))
    ⟨i,hi,mul_pos (hc i hi) hbi⟩

theorem all_counts_from_complete_entrance (P : ℕ → ℕ → Prop)
    (hbase : ∀ u r,u+r ≤ 18 → 0 < u+r → (u ≠ 0 ∨ r ≠ 2) → P u r)
    (hB : ∀ u r,18 ≤ u+r → P u r → P (u+1) r)
    (hT : ∀ u r,18 ≤ u+r → P u r → P u (r+1)) :
    ∀ u r,0 < u+r → (u ≠ 0 ∨ r ≠ 2) → P u r := by
  have hall : ∀ w u r,u+r=w → 0 < w → (u ≠ 0 ∨ r ≠ 2) → P u r := by
    intro w
    induction w using Nat.strong_induction_on with
    | h w ih =>
        intro u r he hw hn
        by_cases hb : w ≤ 18
        · exact hbase u r (by omega) (by omega) hn
        · cases r with
          | succ r =>
              have hp := ih (u+r) (by omega) u r rfl (by omega) (by omega)
              exact hT u r (by omega) hp
          | zero =>
              cases u with
              | zero => omega
              | succ u =>
                  have hp := ih (u+0) (by omega) u 0 rfl (by omega) (by omega)
                  exact hB u 0 (by omega) hp
  intro u r hw hn
  exact hall (u+r) u r rfl hw hn

theorem excluded_pure_two_negative_minor (x : ℝ) (hl : 1 < x) (hu : x < 2) :
    x^2-3*x+2 < 0 := by
  have h := mul_neg_of_pos_of_neg (show 0 < x-1 by linarith) (show x-2 < 0 by linarith)
  nlinarith

#print axioms root_interval_from_cubic_endpoint_signs
#print axioms quadratic_interval_lower_bound
#print axioms strict_finite_Bernstein_combination
#print axioms all_counts_from_complete_entrance
#print axioms excluded_pure_two_negative_minor

end TribonacciInverseClosure
