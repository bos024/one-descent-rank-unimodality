import Mathlib

set_option maxHeartbeats 0

namespace InfinitePaddingFullDeficit

theorem golden_upper_five_eighths (q : ℝ)
    (hq : q^2+q=1) (hq0 : 0 ≤ q) : q < 5/8 := by
  by_contra h
  have hlow : 5/8 ≤ q := by linarith only [h]
  have hp := mul_nonneg (show 0 ≤ q-5/8 by linarith only [hlow])
    (show 0 ≤ q+5/8 by linarith only [hq0])
  nlinarith only [hp,hq,hlow]

theorem final_ulc_factor_payment (u k : ℝ)
    (hu : 3 ≤ u) (hk : k ≤ u-1) :
    u*(u-k+1)/2 ≤ (u-k)*(u+1) := by
  have hp := mul_nonneg (show 0 ≤ u-k-1 by linarith only [hk])
    (show 0 ≤ u+2 by linarith only [hu])
  nlinarith only [hp,hu]

theorem entire_final_geometric_power_bound (q : ℝ)
    (hq : q^2+q=1) (hqlo : 3/5 ≤ q) (hqhi : q ≤ 2/3) :
    ∀ k : ℕ, q^(k+5)*((k:ℝ)+6+q) ≤ 32/45 := by
  have hq0 : 0 ≤ q := by linarith only [hqlo]
  have hq2 : q^2 ≤ 2/5 := by linarith only [hq,hqlo]
  have hq4 : q^4 ≤ 4/25 := by
    have ht := mul_self_le_mul_self (sq_nonneg q) hq2
    nlinarith only [ht]
  have hq5 : q^5 ≤ 8/75 := by
    calc
      q^5 = q*q^4 := by ring
      _ ≤ (2/3)*(4/25) := mul_le_mul hqhi hq4 (pow_nonneg hq0 _) (by norm_num)
      _ = 8/75 := by norm_num
  intro k
  induction k with
  | zero =>
    norm_num only [Nat.cast_zero,zero_add]
    have hp := mul_le_mul hq5
      (show 6+q ≤ (20:ℝ)/3 by linarith only [hqhi])
      (show 0 ≤ 6+q by linarith only [hq0]) (by norm_num : (0:ℝ) ≤ 8/75)
    norm_num at hp
    exact hp
  | succ k ih =>
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hs : q*((k:ℝ)+7+q) ≤ (k:ℝ)+6+q := by
      have hp := mul_le_mul_of_nonneg_right hqhi
        (show 0 ≤ (k:ℝ)+7+q by linarith only [hk0,hq0])
      nlinarith only [hp,hk0,hq0]
    have hp := mul_le_mul_of_nonneg_left hs (pow_nonneg hq0 (k+5))
    have heq : q^(k+1+5)*((k:ℝ)+7+q)
        = q^(k+5)*(q*((k:ℝ)+7+q)) := by
      rw [show k+1+5=(k+5)+1 by omega,pow_succ]
      ring
    norm_num only [Nat.cast_succ] at ⊢
    convert le_trans (show q^(k+1+5)*((k:ℝ)+7+q)
      ≤ q^(k+5)*((k:ℝ)+6+q) by rw [heq]; exact hp) ih using 1
    ring

theorem final_large_kernel_quantitative_margin
    (P v Qs Qk T K : ℝ) (hP : 0 ≤ P) (hQk : 0 ≤ Qk)
    (hQs : 3/2 ≤ Qs) (hT : T ≤ v*Qk)
    (hdecay : P*v ≤ 32/45)
    (hK : Qs*Qk/2 ≤ K) :
    (7/180)*Qk ≤ K-P*T := by
  have h1 := mul_nonneg hQk (show 0 ≤ Qs-3/2 by linarith only [hQs])
  have h2 := mul_nonneg hP (show 0 ≤ v*Qk-T by linarith only [hT])
  have h3 := mul_nonneg hQk (show 0 ≤ 32/45-P*v by linarith only [hdecay])
  nlinarith only [h1,h2,h3,hK]

theorem twelve_small_final_rows (q : ℝ) (hq : q < 5/8) :
    0 < 5-3*(1+q) ∧ 0 < 26-15*(1+q) ∧ 0 < 27-16*(1+q) ∧
    0 < 28-17*(1+q) ∧ 0 < 81-48*(1+q) ∧
    0 < 103-61*(1+q) ∧ 0 < 55-33*(1+q) ∧
    0 < 38-23*(1+q) ∧ 0 < 264-160*(1+q) ∧
    0 < 574-349*(1+q) ∧ 0 < 588-359*(1+q) ∧
    0 < 277-170*(1+q) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals linarith only [hq]

#print axioms golden_upper_five_eighths
#print axioms final_ulc_factor_payment
#print axioms entire_final_geometric_power_bound
#print axioms final_large_kernel_quantitative_margin
#print axioms twelve_small_final_rows

end InfinitePaddingFullDeficit
