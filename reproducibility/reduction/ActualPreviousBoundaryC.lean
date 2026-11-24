import Mathlib

namespace ActualPreviousBoundaryC

theorem three_four_norm_lower (q : ℝ) (hq : 0<q) (heq : q^2+q=1) :
    q^2 < 2*q^3*(1-q^4) := by
  have hid : 2*q^3*(1-q^4)-q^2=q^8 := by
    linear_combination (q^2-q^3-q^5-q^6)*heq
  nlinarith [pow_pos hq 8]

theorem conjugate_atom_lower (q rho : ℝ) (hq : 0<q)
    (heq : q^2+q=1) (hr : q^2<rho) : q+1<(q+1)^3*rho := by
  have hm : q*(q+1)=1 := by nlinarith
  have hid : (q+1)^3*q^2=q+1 := by
    calc
      _ = (q+1)*(q*(q+1))^2 := by ring
      _ = q+1 := by rw [hm]; ring
  have hp := mul_lt_mul_of_pos_left hr (show 0<(q+1)^3 by positivity)
  nlinarith

theorem positive_head_at_least_one (q f e : ℝ) (hq : 0<q)
    (heq : q^2+q=1) (he : 3≤e) (hf : q^2*e≤f) : 1<f := by
  have hupper : q<(2:ℝ)/3 := by nlinarith [sq_nonneg (q-2/3)]
  nlinarith

theorem base_two_head_payment (q f atom : ℝ) (heq : q^2+q=1)
    (hf : 1≤f) (ha : 0<atom) : 0<f+2*(q+1)-(q+1)^3+atom := by
  have hphi : (q+1)^3=2*(q+1)+1 := by
    linear_combination (q+2)*heq
  rw [hphi]
  linarith

theorem base_one_head_payment (q f atom : ℝ) (heq : q^2+q=1)
    (hf : 1≤f) (ha : q+1<atom) : 0<f+(q+1)-(q+1)^3+atom := by
  have hphi : (q+1)^3=2*(q+1)+1 := by
    linear_combination (q+2)*heq
  rw [hphi]
  linarith

theorem previous_CI_bonus (r eps : ℝ) (hr : 2≤r) (he : eps≤1) :
    r≤r*(r+1)/2-eps := by nlinarith

theorem earlier_symmetric_row_geometry (h u k : ℤ)
    (hh : 3*u+6≤h) (hk : k≤u-1) : h+3*k≤2*h-7 := by omega

theorem previous_boundary_read_guard (h u r R : ℤ)
    (hR : h-u-2≤R) : h+r-1-R≤u+r+1 := by omega

theorem five_gap_all_shifts_guard (h u r R : ℤ)
    (hu : h-5≤u) (hR : 3≤R) : h+r-1-R≤u+r+1 := by omega

theorem eight_gap_wedge_or_small (w delta : ℤ) (hd : delta≤8)
    (hn : 4*w+17<13*delta) : w+delta≤29 := by omega

theorem protected_previous_current (h u r : ℤ) (hu : h-2≤u) :
    h+r-1≤u+r+1 := by omega

#print axioms three_four_norm_lower
#print axioms conjugate_atom_lower
#print axioms positive_head_at_least_one
#print axioms base_two_head_payment
#print axioms base_one_head_payment
#print axioms previous_CI_bonus
#print axioms earlier_symmetric_row_geometry
#print axioms previous_boundary_read_guard
#print axioms five_gap_all_shifts_guard
#print axioms eight_gap_wedge_or_small
#print axioms protected_previous_current

end ActualPreviousBoundaryC
