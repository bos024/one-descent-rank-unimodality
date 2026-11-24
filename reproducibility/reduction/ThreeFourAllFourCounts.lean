import Mathlib
set_option maxHeartbeats 3000000
namespace ThreeFourAllFourCounts

theorem whole_near_phase_damped_payment (b : ℝ) (s n : ℕ)
    (hb : 1/2≤b) (hb6 : b≤6/11) (hs : 18 ≤ s) (hn : 3*s≤n+2) :
    10*(2:ℝ)^s*b^(n/2)<1 := by
  have hb0 : 0≤b := by linarith
  have hb1 : b≤1 := by linarith
  have he : 3*s≤2*(n/2)+3 := by omega
  have hp := pow_le_pow_of_le_one hb0 hb1 he
  have hid : b^(2*(n/2)+3)=(b^(n/2))^2*b^3 := by
    rw [pow_add,Nat.mul_comm 2 (n/2),pow_mul]
  rw [hid] at hp
  have h2 : ((2:ℝ)^s)^2=(4:ℝ)^s := by simp only [sq,← mul_pow]; norm_num
  have hscaled : (((2:ℝ)^s*b^(n/2))^2)*b^3≤(4*b^3)^s := by
    have h := mul_le_mul_of_nonneg_left hp (show 0≤(4:ℝ)^s by positivity)
    rw [pow_mul] at h
    rw [mul_pow,h2,mul_pow]
    nlinarith only [h]
  have bmin : (1/8:ℝ)≤b^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hb 3
    norm_num at h
    exact h
  have qmax : 4*b^3≤(2/3:ℝ) := by
    have h := pow_le_pow_left₀ hb0 hb6 3
    nlinarith only [h]
  have hq : (4*b^3)^s≤(2/3:ℝ)^18 := by
    apply le_trans (pow_le_pow_left₀ (by positivity) qmax s)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hmin := mul_le_mul_of_nonneg_left bmin (sq_nonneg ((2:ℝ)^s*b^(n/2)))
  have hsquare : (10*((2:ℝ)^s*b^(n/2)))^2<1 := by
    have hnum : (800:ℝ)*(2/3:ℝ)^18<1 := by norm_num
    nlinarith only [hscaled,hq,hmin,hnum]
  nlinarith only [hsquare,sq_nonneg (10*((2:ℝ)^s*b^(n/2))-1)]

theorem entire_analytic_diagonal_and_phase_cover (r s : ℕ) (hr : 50 ≤ r) :
    let s0 := (r+4)/3
    18 ≤ s0 ∧ r+2 ≤ 3*s0 ∧ 3*s0 ≤ r+4 ∧
    (s < s0 → 3*s ≤ r+3) ∧
    (s0 ≤ s → r+2 ≤ 3*s) ∧
    (3*s ≤ r+4 → 18 ≤ max s 18 ∧ 3*(max s 18) ≤ r+4) ∧
    s0+4 ≤ r+s0+1 := by
  dsimp
  omega

theorem whole_norm_and_tilt_monotone_in_count (b : ℝ) (r s S n : ℕ)
    (hb : 0≤b) (hS : s ≤ S) :
    b^(r+1)*(4:ℝ)^s≤b^(r+1)*(4:ℝ)^S ∧
    (2:ℝ)^s*b^(n/2)≤(2:ℝ)^S*b^(n/2) := by
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hS) (by positivity)
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hS) (by positivity)

theorem exact_next_only_first_defect_join (x y z delta : ℝ)
    (hx : 0≤x) (hd : 1≤delta) (hM : -x≤y^2-x*z) :
    0≤y^2-x*(z-delta) := by
  have h := mul_nonneg hx (show 0≤delta-1 by linarith)
  nlinarith only [h,hM]

#print axioms whole_near_phase_damped_payment
#print axioms entire_analytic_diagonal_and_phase_cover
#print axioms whole_norm_and_tilt_monotone_in_count
#print axioms exact_next_only_first_defect_join
end ThreeFourAllFourCounts
