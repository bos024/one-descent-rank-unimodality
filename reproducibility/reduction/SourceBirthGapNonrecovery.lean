import Mathlib

namespace SourceBirthGapNonrecovery

theorem birth_term_dominates
    {ι : Type*} (S : Finset ι) (birth : ι) (w f : ι → ℝ)
    (hb : birth∈S) (hw : ∀ i∈S, 0 ≤ w i) (hf : ∀ i∈S, 0 ≤ f i)
    (hwb : 1 ≤ w birth) : f birth ≤ ∑ i∈S, w i*f i := by
  calc
    f birth ≤ w birth*f birth := by nlinarith [hf birth hb]
    _ ≤ ∑ i∈S, w i*f i := Finset.single_le_sum (fun i hi => mul_nonneg (hw i hi) (hf i hi)) hb

theorem skeleton_relative_curvature_bound
    (r D K KNext d dNext : ℝ) (hK : 0 < K) (hd : 0 ≤ d) (hr : 0 ≤ r+1)
    (hrel : dNext*K ≤ d*KNext) (hbox : (r+1)*KNext ≤ (D-r)*K) :
    (r+1)*(dNext-d) ≤ (D-2*r-1)*d := by
  have h1 := mul_le_mul_of_nonneg_left hrel hr
  have h2 := mul_le_mul_of_nonneg_left hbox hd
  have hp : K*((r+1)*dNext) ≤ K*((D-r)*d) := by nlinarith
  have hh : (r+1)*dNext ≤ (D-r)*d := by
    by_contra! hc
    have hz := mul_pos hK (sub_pos.mpr hc)
    nlinarith
  nlinarith

theorem reflected_source_index_sum
    (a alpha D h r k excess : ℤ)
    (ha : a=alpha+D+h) (he : excess=2*r+k-(a-h)) :
    (r-excess+1)+(r+k-1)=a-h := by omega

theorem one_step_central_ratio_payment (r e : ℝ) (hr : 10 ≤ r) (he : e ≤ 2) :
    e+1 ≤ r+1 := by linarith

theorem two_step_central_ratio_payment (r : ℝ) (hr : 10 ≤ r) :
    2*(3*r+2) ≤ r*(r+1) := by
  have hp := mul_nonneg (show 0 ≤ r-10 by linarith) (show 0 ≤ r by linarith)
  nlinarith

theorem three_step_central_ratio_payment (r : ℝ) (hr : 10 ≤ r) :
    3*(3*r+1) ≤ (r+1)*(r-1) := by
  have hp := mul_nonneg (show 0 ≤ r-10 by linarith) (show 0 ≤ r by linarith)
  nlinarith

theorem source_birth_pays_recovery
    (sourceDifference birthCoefficient primitiveCurvature : ℝ)
    (hsource : birthCoefficient ≤ sourceDifference)
    (hbirth : primitiveCurvature ≤ birthCoefficient) :
    primitiveCurvature-sourceDifference ≤ 0 := by linarith

theorem unbounded_to_near_center_strip
    (a alpha D h r k : ℤ) (ha : a=alpha+D+h)
    (hcurve : 2*r+2 ≤ D) (hgap : k-alpha ≤ 5)
    (hlate : 0 < 2*r+k-(a-h)) :
    0 ≤ D-2*r-2 ∧ D-2*r-2 ≤ 2 ∧
    3 ≤ k-alpha ∧ k-alpha ≤ 5 ∧
    1 ≤ 2*r+k-(a-h) ∧ 2*r+k-(a-h) ≤ 3 := by omega

#print axioms birth_term_dominates
#print axioms skeleton_relative_curvature_bound
#print axioms reflected_source_index_sum
#print axioms one_step_central_ratio_payment
#print axioms two_step_central_ratio_payment
#print axioms three_step_central_ratio_payment
#print axioms source_birth_pays_recovery
#print axioms unbounded_to_near_center_strip

end SourceBirthGapNonrecovery
