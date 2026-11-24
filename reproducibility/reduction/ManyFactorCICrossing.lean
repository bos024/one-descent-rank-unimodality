import Mathlib

set_option maxHeartbeats 0

namespace ManyFactorCICrossing

theorem interior_unscaled_five_fourths (u q : ℝ) (hu : 16 ≤ u)
    (hq : q ≤ 2/3) :
    (5/4)*(u+2)^2*(u+q) ≤ 2*(u+1)*(u-1)*(u-2) := by
  have hx : 0 ≤ u-16 := by linarith only [hu]
  have hc : 0 ≤ (u-16)^3 := by positivity
  have hs := sq_nonneg (u-16)
  have h1 := mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq]) (sq_nonneg (u+2))
  nlinarith only [hc,hs,hx,h1]

theorem interior_numerator_zero_row (u : ℝ) (hu : 16 ≤ u) :
    (5/4)*(4*u/3+5/3) ≤ (u-1)*(u-2)/2 := by
  nlinarith only [sq_nonneg (u-16),hu]

theorem stronger_interval_norm_constants (q : ℝ)
    (hqlo : 309/500 ≤ q) (hqhi : q ≤ 5/8) (hroot : q^2+q=1) :
    q+q^6 ≤ 27/40 ∧ (1+q)^2 ≤ 21/8 ∧
    (21/8:ℝ)*(27/40)^6 ≤ 1/4 := by
  have h2 : q^2=1-q := by linarith only [hroot]
  have h3 : q^3=2*q-1 := by
    calc q^3=q*q^2 := by ring
         _=q*(1-q) := by rw [h2]
         _=2*q-1 := by nlinarith only [h2]
  have h6 : q^6=5-8*q := by
    calc q^6=(q^3)^2 := by ring
         _=(2*q-1)^2 := by rw [h3]
         _=5-8*q := by nlinarith only [h2]
  refine ⟨?_,?_,?_⟩
  · linarith only [h6,hqlo]
  · nlinarith only [hroot,hqhi]
  · norm_num

theorem many_factor_nonlong_geometry (u delta r t : ℝ)
    (hr : 6 ≤ r) (hd : 3 ≤ delta)
    (hold : (r-1)*delta ≤ u+delta-t+1) :
    t ≤ u-11 := by
  have hd0 : 0 ≤ delta := by linarith only [hd]
  have h1 := mul_nonneg (show 0 ≤ r-6 by linarith only [hr]) hd0
  nlinarith only [h1,hd,hold]

theorem fast_window_only_three_integer_pairs (u delta : ℕ)
    (hd : 3 ≤ delta) (hm : 5*delta ≤ u)
    (hf : 3*(u+1) < 13*(delta+1)) :
    (u=15 ∧ delta=3) ∨ (u=16 ∧ delta=3) ∨ (u=20 ∧ delta=4) := by
  omega

theorem many_factor_perturbed_junction (u gap err M : ℝ)
    (hu : 16 ≤ u) (hg : 3*u/2 ≤ gap)
    (he : err ≤ u/3+1/6) (hm : 0 ≤ M) :
    0 < M+1+gap-err := by linarith only [hu,hg,he,hm]

theorem discarded_primitive_prefix_is_absent (a n : ℤ) (delta L : ℕ)
    (h : a+(delta:ℤ) ≤ n) (K : ℤ → ℝ)
    (hK : ∀ j, a < j → K j=0)
    (f g : ℕ → ℝ) (hfg : ∀ j, delta ≤ j → f j=g j) :
    (∑ j ∈ Finset.range L, K (n-(j:ℤ))*f j)
      = ∑ j ∈ Finset.range L, K (n-(j:ℤ))*g j := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : delta ≤ j
  · rw [hfg j hz]
  · have hn : a < n-(j:ℤ) := by omega
    rw [hK _ hn]
    simp only [zero_mul]

#print axioms interior_unscaled_five_fourths
#print axioms interior_numerator_zero_row
#print axioms stronger_interval_norm_constants
#print axioms many_factor_nonlong_geometry
#print axioms fast_window_only_three_integer_pairs
#print axioms many_factor_perturbed_junction
#print axioms discarded_primitive_prefix_is_absent

end ManyFactorCICrossing
