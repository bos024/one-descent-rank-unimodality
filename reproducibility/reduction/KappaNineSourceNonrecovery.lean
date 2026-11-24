import Mathlib

namespace KappaNineSourceNonrecovery

theorem simultaneous_compulsory_source_payment
    {ι : Type*} (S : Finset ι) (w lower f : ι → ℝ)
    (hf : ∀ i∈S, 0 ≤ f i) (hw : ∀ i∈S, lower i ≤ w i) :
    (∑ i∈S, lower i*f i) ≤ ∑ i∈S, w i*f i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (hw i hi) (hf i hi)

theorem relative_CI_payment_closes_curvature
    (r e C d source lower : ℝ) (hr : 0 < r+1) (hd : 0 ≤ d)
    (hcurve : (r+1)*C ≤ (e+1)*d)
    (hsource : lower*d ≤ source) (hlower : e+1 ≤ (r+1)*lower) :
    C ≤ source := by
  have hp := mul_le_mul_of_nonneg_right hlower hd
  have hs := mul_le_mul_of_nonneg_left hsource (le_of_lt hr)
  have ht : (r+1)*C ≤ (r+1)*source := by nlinarith
  by_contra! hn
  have hz := mul_pos hr (sub_pos.mpr hn)
  nlinarith

theorem kappa_nine_canonical_rank_bounds
    (alpha r e D : ℤ) (ha : alpha=1 ∨ alpha=2)
    (_hr : 0 ≤ r) (he : 0 ≤ e) (hstrip : e ≤ 6-alpha)
    (hD : D=2*r+2+e)
    (hbound : D ≤ min (2*(9-alpha)*(6-alpha)) (12*(9-alpha)-25)) :
    (alpha=1 ∧ r ≤ 34 ∧ e ≤ 5 ∧ D ≤ 71) ∨
    (alpha=2 ∧ r ≤ 27 ∧ e ≤ 4 ∧ D ≤ 56) := by
  rcases ha with ha | ha
  · subst alpha
    norm_num at hbound
    omega
  · subst alpha
    norm_num at hbound
    omega

theorem negative_rank_birth_present
    (D h alpha : ℤ) (hD : h ≤ D) (hh : 6 ≤ h) (ha : 1 ≤ alpha) :
    0 ≤ D+h+2-(9-alpha) := by omega

#print axioms simultaneous_compulsory_source_payment
#print axioms relative_CI_payment_closes_curvature
#print axioms kappa_nine_canonical_rank_bounds
#print axioms negative_rank_birth_present

end KappaNineSourceNonrecovery
