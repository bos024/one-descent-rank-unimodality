import Mathlib

set_option maxHeartbeats 0
namespace RelativeCClosure

theorem positive_tilt_kernel (a : ℝ) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ (if n=0 then (1:ℝ) else 2*(1-a)+((n:ℝ)-1)*(1-a)^2) := by
  by_cases hn : n=0
  · simp [hn]
  · have hn1 : 1 ≤ n := by omega
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
    simp only [hn,ite_false]
    have hh := mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) (sq_nonneg (1-a))
    have hp : 0 ≤ 1-a := by linarith
    nlinarith only [hh,hp]

theorem rational_tilt_identity (a z lam Q : ℝ)
    (ha : a≠0) (hz : 1-z≠0) (haz : 1-a*z≠0) :
    a^2*(1-a*lam*z)*(1+(Q-1)/a^2)/(1-z)^2 =
      ((1-a*z)/(1-z))^2*((1-a*lam*z)*Q/(1-a*z)^2)+
        (a^2-1)*(1-a*lam*z)/(1-z)^2 := by
  field_simp
  ring

theorem twice_cumulative_universal_ratio (F : ℕ → ℝ) (k : ℕ)
    (hmono : ∀ i, i < k → F i ≤ F k) :
    ((k:ℝ)+1)*(∑ i ∈ Finset.range k, F i) ≤
      (k:ℝ)*((∑ i ∈ Finset.range k, F i)+F k) := by
  have hs : (∑ i ∈ Finset.range k, F i) ≤ (k:ℝ)*F k := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, F k := by
        apply Finset.sum_le_sum
        intro i hi
        exact hmono i (Finset.mem_range.mp hi)
      _ = _ := by simp
  nlinarith only [hs]

theorem low_threshold_payment (k : ℕ) (hk : 1 ≤ k) (G Gprev mu : ℝ)
    (hGp : 0 ≤ Gprev) (hbase : ((k:ℝ)+1)*Gprev ≤ (k:ℝ)*G)
    (hmu : mu*(k:ℝ) ≤ (k:ℝ)+1) : 0 ≤ G-mu*Gprev := by
  have hp := mul_nonneg hGp (sub_nonneg.mpr hmu)
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hh : 0 ≤ (k:ℝ)*(G-mu*Gprev) := by nlinarith only [hp,hbase]
  exact (mul_nonneg_iff_of_pos_left hk0).mp hh

theorem high_threshold_payment (a mu G Gprev S : ℝ) (k : ℕ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hS : 0 ≤ S)
    (hmu : (k:ℝ)+1 ≤ mu*(k:ℝ))
    (hid : a^2*(G-mu*Gprev)=S+(a^2-1)*(1+(k:ℝ)*(1-mu))) :
    0 ≤ G-mu*Gprev := by
  have hsmall : a^2-1 ≤ 0 := by nlinarith
  have hc : 1+(k:ℝ)*(1-mu) ≤ 0 := by nlinarith only [hmu]
  have hp := mul_nonneg_of_nonpos_of_nonpos hsmall hc
  have hs : 0 ≤ a^2*(G-mu*Gprev) := by linarith
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hs

theorem complete_positive_kernel_tilt_payment (a lam G Gprev : ℝ) (k : ℕ)
    (H K : ℕ → ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hk : 1 ≤ k)
    (hGp : 0 ≤ Gprev) (hbase : ((k:ℝ)+1)*Gprev ≤ (k:ℝ)*G)
    (hH : ∀ i, i ≤ k → 0 ≤ H i) (hK : ∀ n, 0 ≤ K n)
    (hid : a^2*(G-a*lam*Gprev)=
      (∑ i ∈ Finset.range (k+1), K (k-i)*a^i*H i)+
        (a^2-1)*(1+(k:ℝ)*(1-a*lam))) :
    0 ≤ G-a*lam*Gprev := by
  by_cases hlow : a*lam*(k:ℝ) ≤ (k:ℝ)+1
  · exact low_threshold_payment k hk G Gprev (a*lam) hGp hbase hlow
  · apply high_threshold_payment a (a*lam) G Gprev _ k ha ha1 _ (by linarith) hid
    apply Finset.sum_nonneg
    intro i hi
    have hi0 : i ≤ k := by have hs := Finset.mem_range.mp hi; omega
    exact mul_nonneg (mul_nonneg (hK _) (pow_nonneg (le_of_lt ha) i)) (hH i hi0)

theorem normalized_tilt_density_order (rho : ℕ → ℝ) (a : ℝ) (N : ℕ)
    (ha : 0 < a)
    (hstep : ∀ i, i+1 ≤ N → a*rho i ≤ rho (i+1)) :
    ∀ i, i+1 ≤ N → rho i*a^(i+1) ≤ rho (i+1)*a^i := by
  intro i hi
  have hp := mul_le_mul_of_nonneg_right (hstep i hi) (pow_nonneg (le_of_lt ha) i)
  rw [pow_succ]
  nlinarith only [hp]

#print axioms positive_tilt_kernel
#print axioms rational_tilt_identity
#print axioms twice_cumulative_universal_ratio
#print axioms low_threshold_payment
#print axioms high_threshold_payment
#print axioms complete_positive_kernel_tilt_payment
#print axioms normalized_tilt_density_order
end RelativeCClosure
