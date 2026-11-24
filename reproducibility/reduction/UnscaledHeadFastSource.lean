import Mathlib

set_option maxHeartbeats 0

namespace UnscaledHeadFastSource

theorem uniform_rank_factor (u s k : ℝ) (_hu : 16 ≤ u)
    (hk : 1 ≤ k) (hks : k ≤ s) (hs : s ≤ u-3) :
    4*(s+1)*(u-k+1) ≤ (u+2)^2*(s+1-k) := by
  have ha : 0 ≤ s-k := by linarith only [hks]
  have hb : 0 ≤ u-s := by linarith only [hs]
  have hc : 0 ≤ s+1-k := by linarith only [hks]
  have h1 := mul_nonneg ha hb
  have h2 := mul_nonneg hc (sq_nonneg (u-2*s))
  have h3 := mul_nonneg (show 0 ≤ s+1 by linarith only [hk,hks]) h1
  nlinarith only [h2,h3]

theorem unscaled_interior_scalar (u q : ℝ) (hu : 32 ≤ u)
    (hq : q ≤ 2/3) :
    (8/5)*(u+2)^2*(u+q) ≤ 2*(u+1)*(u-1)*(u-2) := by
  have hx : 0 ≤ u-32 := by linarith only [hu]
  have hc : 0 ≤ (u-32)^3 := by positivity
  have hs := sq_nonneg (u-32)
  have h1 := mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq]) (sq_nonneg (u+2))
  nlinarith only [hc,hs,hx,h1]

theorem penultimate_lower_factor (u k : ℝ) (hu : 32 ≤ u)
    (_hk : 1 ≤ k) (hkh : 2*k ≤ u) :
    2*(u-1)*(u-k+1) ≤ 3*(u+1)*(u-1-k) := by
  have h1 := mul_nonneg (show 0 ≤ u+5 by linarith only [hu])
    (show 0 ≤ u-2*k by linarith only [hkh])
  nlinarith only [h1,sq_nonneg (u-32),hu]

theorem penultimate_two_payments (u : ℝ) (hu : 32 ≤ u) :
    (8/5)*(u/2+2) ≤ u ∧
    (8/5)*(u/5+29/15) ≤ u/2 := by constructor <;> linarith only [hu]

theorem penultimate_coefficient_lower (u p : ℝ) (hu : 32 ≤ u)
    (hp : 8/5 ≤ p) (hp2 : p^2 ≤ 8/3) :
    3*u/2 ≤ p*u-p^2 := by
  have h1 := mul_nonneg (show 0 ≤ p-8/5 by linarith only [hp])
    (show 0 ≤ u by linarith only [hu])
  nlinarith only [h1,hp2,hu]

theorem unscaled_zero_row (u q : ℝ) (hu : 32 ≤ u) (hq : q ≤ 2/3) :
    (8/5)*(3*u/2+q) ≤ (u-1)*(u-2)/2 := by
  nlinarith only [sq_nonneg (u-32),hu,hq]

theorem fast_source_raw_minor (xm x xp em e ep R : ℝ)
    (hlc : 0 ≤ x^2-xm*xp) (hratio : x ≤ R*xm)
    (hem : 0 ≤ em) (he : 0 ≤ e) (hxp : 0 ≤ xp)
    (hprev : em ≤ xm) (hcur : 2*R*em ≤ e) (hnext : 2*R*e ≤ ep) :
    0 ≤ (x-e)^2-(xm-em)*(xp-ep) := by
  have h1 := mul_nonneg (show 0 ≤ xm-em by linarith only [hprev])
    (show 0 ≤ ep-2*R*e by linarith only [hnext])
  have h2 := mul_nonneg he (show 0 ≤ R*xm-x by linarith only [hratio])
  have h3 := mul_nonneg he (show 0 ≤ e-2*R*em by linarith only [hcur])
  have h4 := mul_nonneg hxp hem
  nlinarith only [hlc,h1,h2,h3,h4]

theorem fast_source_positive_part_LC (xm x xp em e ep R : ℝ)
    (_hxm : 0 ≤ xm) (hx : 0 ≤ x) (hxp : 0 ≤ xp)
    (hem : 0 ≤ em) (he : 0 ≤ e) (_hep : 0 ≤ ep) (hR : 0 < R)
    (hlc : 0 ≤ x^2-xm*xp) (hratio : x ≤ R*xm)
    (hcur : 2*R*em ≤ e) (hnext : 2*R*e ≤ ep) :
    0 ≤ (max (x-e) 0)^2-max (xm-em) 0*max (xp-ep) 0 := by
  by_cases hleft : xm≤em
  · rw [max_eq_right (show xm-em≤0 by linarith only [hleft])]
    simp only [zero_mul,sub_zero]
    exact sq_nonneg _
  by_cases hright : xp≤ep
  · rw [max_eq_right (show xp-ep≤0 by linarith only [hright])]
    simp only [mul_zero,sub_zero]
    exact sq_nonneg _
  have hl : em < xm := by linarith only [hleft]
  have hr : ep < xp := by linarith only [hright]
  have hm : e < x := by
    by_contra hbad
    have hbad' : x ≤ e := by linarith only [hbad]
    have hxm0 : 0 < xm := by linarith only [hem,hl]
    have h1 := mul_nonneg hx (show 0 ≤ R*xm-x by linarith only [hratio])
    have hxx : xm*xp ≤ xm*(R*x) := by nlinarith only [hlc,h1]
    have hxpR : xp ≤ R*x := by
      by_contra hh
      have hp := mul_pos hxm0 (show 0 < xp-R*x by linarith only [hh])
      nlinarith only [hp,hxx]
    have h2 := mul_nonneg (le_of_lt hR) (show 0 ≤ e-x by linarith only [hbad'])
    have h3 := mul_nonneg (le_of_lt hR) he
    nlinarith only [hxpR,h2,h3,hnext,hr]
  rw [max_eq_left (show 0≤x-e by linarith only [hm]),
      max_eq_left (show 0≤xm-em by linarith only [hl]),
      max_eq_left (show 0≤xp-ep by linarith only [hr])]
  exact fast_source_raw_minor xm x xp em e ep R hlc hratio hem he hxp (le_of_lt hl) hcur hnext

theorem binomial_growth_pays_fast_source (u j prev cur : ℝ)
    (hj : 0 < j) (hp : 0 ≤ prev) (hbudget : 13*j ≤ 3*(u+1))
    (hbin : (u-j+1)*prev ≤ j*cur) :
    (10/3)*prev ≤ cur := by
  have h1 := mul_nonneg hp (show 0 ≤ 3*(u-j+1)-10*j by linarith only [hbudget])
  have h2 : j*((10/3)*prev) ≤ j*cur := by nlinarith only [h1,hbin]
  by_contra hh
  have hp := mul_pos hj (show 0 < (10/3)*prev-cur by linarith only [hh])
  nlinarith only [hp,h2]

#print axioms uniform_rank_factor
#print axioms unscaled_interior_scalar
#print axioms penultimate_lower_factor
#print axioms penultimate_two_payments
#print axioms penultimate_coefficient_lower
#print axioms unscaled_zero_row
#print axioms fast_source_raw_minor
#print axioms fast_source_positive_part_LC
#print axioms binomial_growth_pays_fast_source

end UnscaledHeadFastSource
