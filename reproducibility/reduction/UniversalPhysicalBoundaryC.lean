import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

namespace UniversalPhysicalBoundaryC

theorem maximal_margin_normalized_tilt (a lam mu k : ℝ)
    (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hlam0 : 0 ≤ lam)
    (_hlam1 : lam ≤ 2) (hmu : mu=a*lam) (hk : 1 ≤ k) :
    a^2*(2-mu) ≤ (2*(1-a)+(k-1)*(1-a)^2)
      +(2-lam)*(1+k*(1-a)-(2*(1-a)+(k-1)*(1-a)^2))
      +(a^2-1)*(1+k*(1-mu)) := by
  have h := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ k-1 by linarith)
    (show 0 ≤ 1-a by linarith)) (sq_nonneg a)) hlam0
  have hid : (2*(1-a)+(k-1)*(1-a)^2)
      +(2-lam)*(1+k*(1-a)-(2*(1-a)+(k-1)*(1-a)^2))
      +(a^2-1)*(1+k*(1-mu))-a^2*(2-mu)
      =(k-1)*(1-a)*a^2*lam := by rw [hmu]; ring
  nlinarith

theorem moving_ratio_unit_margin (p mu : ℝ)
    (hmu : mu ≤ p) : 2-p ≤ 2-mu := by linarith

theorem low_ratio_cumulative_margin (G P lam c : ℝ)
    (hP : 0 ≤ P) (hF : 1 ≤ G-P) (hlam : lam ≤ 1) (hc : c ≤ 1) :
    c ≤ G-lam*P := by
  nlinarith [mul_nonneg (show 0 ≤ 1-lam by linarith) hP]

theorem margin_at_two_edge_maximum (G P r0 r1 c : ℝ)
    (h0 : c ≤ G-P) (h1 : c ≤ G-r0*P) (h2 : c ≤ G-r1*P) :
    c ≤ G-max 1 (max r0 r1)*P := by
  by_cases ht : max r0 r1 ≤ 1
  · simpa [max_eq_left ht] using h0
  · rw [max_eq_right (show 1 ≤ max r0 r1 by linarith)]
    by_cases hh : r0 ≤ r1
    · simpa [max_eq_right hh] using h2
    · simpa [max_eq_left (show r1 ≤ r0 by linarith)] using h1

theorem two_edge_ratio_cap (R : ℕ → ℝ)
    (htail : ∀ n,R (n+1) ≤ max 1 (R 1)) :
    ∀ n,R n ≤ max 1 (max (R 0) (R 1)) := by
  intro n
  cases n with
  | zero => exact le_trans (le_max_left _ _) (le_max_right _ _)
  | succ n =>
      apply le_trans (htail n)
      exact max_le (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem positive_window_cap_transfer (A B mu cap : ℝ)
    (hA : 0<A) (hB : B=mu*A) (hcap : B ≤ cap*A) : mu ≤ cap := by nlinarith

theorem positive_support_window_endpoint (p q A B : ℝ)
    (hid : B-A=q-p) (hp : 0<p) (hg : A<B) : 0<q := by linarith

theorem previous_reference_CDF_margin (G0 G1 c R : ℝ)
    (hbase : c ≤ G0) (hstep : G1=G0+R) (hR : 0 ≤ R) : c ≤ G1 := by linarith

theorem all_large_degree_boundary_rows (u h i : ℕ)
    (hu : 1 ≤ u) (hh : 3*u+3 ≤ h) (hi : i ≤ u-1) :
    h+3*i ≤ 2*(h-3) := by omega

theorem previous_unit_pays_boundary_nondecrease (Cprev Ccur : ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hrow : Ccur ≤ Cprev) :
    Ccur+1 ≤ Cprev+(r:ℝ) := by
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  linarith

theorem small_binary_boundary_complement_weight32 (u h r : ℕ)
    (hu : u ≤ 4) (hh : h<3*u+3) (hr : 2*r ≤ h) :
    h+r ≤ 21 ∧ h+r ≤ 32 := by omega

theorem late_owner_source_read_guard (W j N : ℕ)
    (hW : 1 ≤ W) (hj : W-1 ≤ j) (hN : N=j+1) : W ≤ N := by omega

#print axioms maximal_margin_normalized_tilt
#print axioms moving_ratio_unit_margin
#print axioms low_ratio_cumulative_margin
#print axioms margin_at_two_edge_maximum
#print axioms two_edge_ratio_cap
#print axioms positive_window_cap_transfer
#print axioms positive_support_window_endpoint
#print axioms previous_reference_CDF_margin
#print axioms all_large_degree_boundary_rows
#print axioms previous_unit_pays_boundary_nondecrease
#print axioms small_binary_boundary_complement_weight32
#print axioms late_owner_source_read_guard

end UniversalPhysicalBoundaryC

