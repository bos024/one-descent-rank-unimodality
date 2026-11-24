import Mathlib
set_option maxHeartbeats 3000000
namespace CompleteCapacityFour

theorem complete_cubic_root_entry_damping (b : ℝ) (s m : ℕ)
    (hb : 0 ≤ b) (hb6 : b ≤ 6/11) (hm : 9 ≤ m) (hs : 3*s < m) :
    2*(2:ℝ)^s*b^(m/2)<1 := by
  have hb1 : b ≤ 1 := by linarith
  by_cases hs2 : s ≤ 2
  · have he : 4 ≤ m/2 := by omega
    have hp := pow_le_pow_of_le_one hb hb1 he
    have ht : (2:ℝ)^s ≤ 4 := by
      have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hs2
      norm_num at h; exact h
    have hprod := mul_le_mul ht hp (show 0 ≤ b^(m/2) by positivity) (by norm_num : (0:ℝ) ≤ 4)
    have h4 := pow_le_pow_left₀ hb hb6 4
    have hnum : (8:ℝ)*(6/11)^4<1 := by norm_num
    nlinarith only [hprod,h4,hnum]
  · by_cases hs3 : s=3
    · subst s
      have he : 5 ≤ m/2 := by omega
      have hp := pow_le_pow_of_le_one hb hb1 he
      have h5 := pow_le_pow_left₀ hb hb6 5
      norm_num
      have hnum : (16:ℝ)*(6/11)^5<1 := by norm_num
      nlinarith only [hp,h5,hnum]
    · have hs4 : 4 ≤ s := by omega
      have he : 3*s ≤ 2*(m/2) := by omega
      have hp := pow_le_pow_of_le_one hb hb1 he
      have hid : b^(2*(m/2))=(b^(m/2))^2 := by
        rw [Nat.mul_comm 2 (m/2),pow_mul]
      have hid3 : b^(3*s)=(b^3)^s := by rw [pow_mul]
      rw [hid,hid3] at hp
      have htwo : ((2:ℝ)^s)^2=(4:ℝ)^s := by
        simp only [sq,← mul_pow]; norm_num
      have hp2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ (4:ℝ)^s by positivity)
      have hbound : (2*(2:ℝ)^s*b^(m/2))^2 ≤ 4*(4*b^3)^s := by
        rw [← mul_pow] at hp2
        rw [mul_pow,mul_pow,htwo]
        nlinarith only [hp2]
      have hc := pow_le_pow_left₀ hb hb6 3
      have hq : 4*b^3 ≤ (2/3:ℝ) := by nlinarith only [hc]
      have hq1 := pow_le_pow_left₀ (show 0 ≤ 4*b^3 by positivity) hq s
      have hq2 := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2/3)
        (by norm_num : (2/3:ℝ) ≤ 1) hs4
      have hnum : (4:ℝ)*(2/3)^4<1 := by norm_num
      have hsq : (2*(2:ℝ)^s*b^(m/2))^2<1 := by nlinarith only [hbound,hq1,hq2,hnum]
      nlinarith only [hsq,sq_nonneg (2*(2:ℝ)^s*b^(m/2)-1)]

theorem all_seven_small_cubic_root_entries (l : ℝ) (hl : 1839/1000 ≤ l) :
    0 < 8*l-13 ∧ 0 < 14*l-25 ∧ 0 < 26*l-47 ∧
    0 < 48*l-87 ∧ 0 < 96*l-175 ∧ 0 < 88*l-161 ∧ 0 < 176*l-323 := by
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem complete_unit_minor_parameter_partition (r s : ℕ)
    (_hr : 1 ≤ r) (hs : 1 ≤ s) :
    r+s ≤ 10 ∨ 18 ≤ s ∨ (57 ≤ r ∧ s ≤ 17) ∨
      (r ≤ 56 ∧ s ≤ 17 ∧ 11 ≤ r+s) := by omega

theorem complete_binary_seed_jet_padding_clamp (u a : ℕ) (hu : 1 ≤ u) :
    (7 ≤ u → 6 < u+1) ∧ (7 ≤ a → 6 < a+u+1) := by omega

theorem complete_actual_base_all_padding_clamp (L w a : ℕ)
    (ha : L-w+1 ≤ a) : L < a+w+1 := by omega

theorem complete_all_three_binary_four_count_base_selection (r u s : ℕ)
    (hr : 1 ≤ r) :
    (r=1 ∧ s ≤ 1) ∨ (2 ≤ r ∧ u ≤ 2*r) ∨
    (r=1 ∧ u ≤ 8 ∧ 2 ≤ s) ∨ (2*r+3*s ≤ u) ∨
    (2*r < u ∧ (u-2*r)/3+1 ≤ s ∧ (r=1 → 3 ≤ (u-2*r)/3+1)) := by
  have hm := Nat.mod_lt (u-2*r) (by norm_num : 0 < 3)
  have he := Nat.mod_add_div (u-2*r) 3
  omega

end CompleteCapacityFour
#print axioms CompleteCapacityFour.complete_cubic_root_entry_damping
#print axioms CompleteCapacityFour.all_seven_small_cubic_root_entries
#print axioms CompleteCapacityFour.complete_unit_minor_parameter_partition
#print axioms CompleteCapacityFour.complete_binary_seed_jet_padding_clamp
#print axioms CompleteCapacityFour.complete_actual_base_all_padding_clamp
#print axioms CompleteCapacityFour.complete_all_three_binary_four_count_base_selection
