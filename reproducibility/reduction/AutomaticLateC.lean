import Mathlib

set_option maxHeartbeats 0

namespace AutomaticLateC

theorem improved_symmetric_row_geometry (u h : ℝ)
    (hh : 3*u-1 ≤ h) : (3*u-4+h)/2 ≤ h-3/2 := by
  linarith only [hh]

theorem large_interval_degree_geometry (u h t : ℝ)
    (ht : 2*u ≤ t) : 2*u-2+h-(t-1) ≤ h-1 := by
  linarith only [ht]

theorem source_body_read_before_midpoint (u h alpha : ℝ)
    (hh : h ≤ 3*u) (ha : 1 ≤ alpha) :
    h-u-alpha ≤ (h+u)/2 := by linarith only [hh,ha]

theorem actual_first_tail_boundary_payment (prev cur oldSource nextSource : ℝ)
    (hC : cur-prev ≤ 1) (hE : oldSource ≤ nextSource) :
    cur-nextSource ≤ prev+1-oldSource := by linarith only [hC,hE]

theorem small_binary_remainder_weight32 (u h r : ℝ)
    (hu : u ≤ 7) (hh : h ≤ 3*u-2) (hr : 2*r ≤ h) :
    h+r ≤ 32 := by linarith only [hu,hh,hr]

theorem unique_eighth_count_geometry (h r : ℝ)
    (hh : h ≤ 22) (hr : 2*r ≤ h) (hW : 33 ≤ h+r) :
    h=22 ∧ r=11 := by constructor <;> linarith only [hh,hr,hW]

#print axioms improved_symmetric_row_geometry
#print axioms large_interval_degree_geometry
#print axioms source_body_read_before_midpoint
#print axioms actual_first_tail_boundary_payment
#print axioms small_binary_remainder_weight32
#print axioms unique_eighth_count_geometry

end AutomaticLateC
