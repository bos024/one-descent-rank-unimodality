import Mathlib

namespace PhysicalBoundaryGoldenC

theorem previous_CI_units (P c0 c1 c2 r : ℝ)
    (F0 F1 F2 : ℝ) (h0 : F0=P+c0) (h1 : F1=P-1+c1)
    (h2 : F2=P-r-1+c2) : F0-F1=c0-c1+1 ∧ F1-F2=c1-c2+r := by
  constructor <;> linarith

theorem degree_two_gap_payment (q rho : ℝ) (hq : 0<q)
    (heq : q^2+q=1) (hr : rho<1) : 0<(q+1)+1-(q+1)^2*rho := by
  have hphi : (q+1)^2=(q+1)+1 := by nlinarith
  rw [hphi]
  nlinarith

theorem positive_head_gap_payment (q f atom : ℝ) (heq : q^2+q=1)
    (hf : 2*q^2≤f) (ha : atom≤2) : q^2≤(q+1)+f-atom := by
  nlinarith

theorem multiple_factor_norm_payment (q atom : ℝ) (hq : 0<q)
    (heq : q^2+q=1) (ha : atom≤4*q^2) : 0<(q+1)-atom := by
  have hl : (3:ℝ)/5<q := by nlinarith [sq_nonneg (q-3/5)]
  nlinarith

theorem large_degree_row_geometry (h u k : ℤ) (_hu : 1 ≤ u)
    (hh : 3 * u + 3 ≤ h) (_hk0 : 0 ≤ k) (hk : k ≤ u - 1) :
    h + 3 * k ≤ 2 * h - 5 := by omega

theorem nonincreasing_CI_row_entry (phi cprev ccur r : ℝ)
    (hp : 1<phi) (hc : ccur≤cprev) (hr : 1≤r)
    (ha : 0<cprev+r) : ccur+1<phi*(cprev+r) := by nlinarith

theorem boundary_C_read_guard (h u r R : ℤ)
    (hR : h-u-1≤R) : h+r-R≤u+r+1 := by omega

theorem four_gap_all_shift_guard (h u r R : ℤ)
    (hcount : h-4≤u) (hR : 3≤R) : h+r-R≤u+r+1 := by omega

#print axioms previous_CI_units
#print axioms degree_two_gap_payment
#print axioms positive_head_gap_payment
#print axioms multiple_factor_norm_payment
#print axioms large_degree_row_geometry
#print axioms nonincreasing_CI_row_entry
#print axioms boundary_C_read_guard
#print axioms four_gap_all_shift_guard

end PhysicalBoundaryGoldenC
