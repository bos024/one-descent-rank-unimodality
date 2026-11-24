import Mathlib

set_option maxHeartbeats 0

namespace ModeOnlyUniformWindow

theorem concave_triple_is_LC (a x b : ℝ) (ha : 0 ≤ a)
    (hconc : a+b ≤ 2*x) : 0 ≤ x^2-a*b := by
  have hp:=mul_nonneg ha (show 0 ≤ 2*x-a-b by linarith only [hconc])
  nlinarith only [hp,sq_nonneg (x-a)]

theorem uniform_transition_payment (a x b enterOld enterNew leaveOld leaveNew : ℝ)
    (ha : 0 ≤ a) (he : enterNew ≤ enterOld) (hl : leaveOld ≤ leaveNew)
    (hprev : x-a=enterOld-leaveOld) (hnext : b-x=enterNew-leaveNew) :
    0 ≤ x^2-a*b := by
  apply concave_triple_is_LC a x b ha
  linarith only [he,hl,hprev,hnext]

theorem signed_transition_is_nonincreasing (prev cur incoming outgoing : ℝ)
    (hi : incoming ≤ 0) (ho : 0 ≤ outgoing)
    (hdef : cur-prev=incoming-outgoing) : cur ≤ prev := by
  linarith only [hi,ho,hdef]

theorem minimal_crossing_geometry (u h d r : ℝ)
    (hu : 0 ≤ u) (hd : 2 ≤ d) (hdu : d ≤ u)
    (hmin : r*d ≤ h) (hdelete : h-d ≤ u) :
    h ≤ 2*u ∧ 2*(r-1) ≤ u := by
  constructor
  · linarith only [hdelete,hdu]
  · by_cases hr : 1 ≤ r
    · have hp:=mul_nonneg (show 0 ≤ d-2 by linarith only [hd]) (show 0 ≤ r-1 by linarith only [hr])
      nlinarith only [hp,hmin,hdelete]
    · linarith only [hu,hr]

#print axioms concave_triple_is_LC
#print axioms uniform_transition_payment
#print axioms signed_transition_is_nonincreasing
#print axioms minimal_crossing_geometry

end ModeOnlyUniformWindow
