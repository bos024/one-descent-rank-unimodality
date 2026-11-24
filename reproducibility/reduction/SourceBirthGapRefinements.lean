import Mathlib

namespace SourceBirthGapRefinements

theorem gap_six_all_large_rank_payments (r : ℝ) (hr : 7 ≤ r) :
    4 ≤ r+1 ∧
    3*(r+5) ≤ (r+1)*r ∧
    2*(r+4)*(r+5) ≤ (r+1)*r*(r-1) ∧
    (r+3)*(r+4)*(r+5) ≤ (r+1)*r*(r-1)*(r-2) := by
  let x := r-7
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have he : r=x+7 := by dsimp [x]; ring
  rw [he]
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg x]
  constructor
  · nlinarith [sq_nonneg x, pow_nonneg hx 3]
  · nlinarith [sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4]

theorem gap_seven_all_large_rank_payments (r : ℝ) (hr : 10 ≤ r) :
    5 ≤ r+1 ∧
    4*(r+6) ≤ (r+1)*r ∧
    3*(r+5)*(r+6) ≤ (r+1)*r*(r-1) ∧
    2*(r+4)*(r+5)*(r+6) ≤ (r+1)*r*(r-1)*(r-2) ∧
    (r+3)*(r+4)*(r+5)*(r+6) ≤ (r+1)*r*(r-1)*(r-2)*(r-3) := by
  let x := r-10
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have he : r=x+10 := by dsimp [x]; ring
  rw [he]
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg x]
  constructor
  · nlinarith [sq_nonneg x, pow_nonneg hx 3]
  constructor
  · nlinarith [sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4]
  · nlinarith [sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]

theorem second_source_growth_increment
    (oldSecond birthOne birthTwo : ℝ) (hOld : 2 ≤ oldSecond)
    (hOne : birthOne ≤ 1) (hTwo : 0 ≤ birthTwo) :
    1 ≤ oldSecond+birthTwo-birthOne := by linarith

theorem second_source_stationary_increment
    (oldConstant oldLinear : ℝ) (hLinear : 1 ≤ oldLinear) :
    1 ≤ (oldConstant+oldLinear)-oldConstant := by linarith

theorem general_early_curvature_growth
    (oldCoefficient previousBirth currentBirth target : ℝ)
    (ht : 1 ≤ target) (hOld : 2*target ≤ oldCoefficient)
    (hPrev : previousBirth ≤ 1) (hCurrent : 0 ≤ currentBirth) :
    target ≤ oldCoefficient+currentBirth-previousBirth := by linarith

theorem tied_multiplicity_curvature_scaling
    (d v : ℝ) (hd : 1 ≤ d) (hv : 0 ≤ v) : (d+1)*v ≤ d*(2*v) := by
  have hp := mul_nonneg (show 0 ≤ d-1 by linarith) hv
  nlinarith

#print axioms gap_six_all_large_rank_payments
#print axioms gap_seven_all_large_rank_payments
#print axioms second_source_growth_increment
#print axioms second_source_stationary_increment
#print axioms general_early_curvature_growth
#print axioms tied_multiplicity_curvature_scaling

end SourceBirthGapRefinements
