import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace TwoFactorCompleteEntrance

theorem transported_minor_term (X Y Z a b : ℝ)
    (hX : 0 < X) (hXY : X ≤ Y) (ha : 0 ≤ a)
    (hlc : X*Z ≤ Y^2) (hd : 0 ≤ b*X-a*Y) :
    b*X-a*Y ≤ b*Y-a*Z := by
  have h1 := mul_nonneg (show 0 ≤ Y-X by linarith only [hXY]) hd
  have h2 := mul_nonneg ha (show 0 ≤ Y^2-X*Z by linarith only [hlc])
  have hp : 0 ≤ X*((b*Y-a*Z)-(b*X-a*Y)) := by nlinarith only [h1,h2]
  have hh := (mul_nonneg_iff_of_pos_left hX).mp hp
  linarith only [hh]

theorem prefix_reference_loss_payment (u x v w a b C F : ℝ)
    (hu : 14 ≤ u) (hx : 0 ≤ x) (hv : x ≤ v) (hw : w ≤ 2*v)
    (ha : 0 ≤ a) (hb : u ≤ b-2*a) (hC : C ≤ 7*x/3)
    (hF : 0 ≤ F) (hFhi : F ≤ 5) :
    0 ≤ b*v-a*w-F*C := by
  have h1 := mul_nonneg ha (show 0 ≤ 2*v-w by linarith only [hw])
  have h2 := mul_nonneg (show 0 ≤ b-2*a-u by linarith only [hb])
    (show 0 ≤ v by linarith only [hx,hv])
  have h3 := mul_nonneg (show 0 ≤ u by linarith only [hu])
    (show 0 ≤ v-x by linarith only [hv])
  have h4 := mul_nonneg hF (show 0 ≤ 7*x/3-C by linarith only [hC])
  have h5 := mul_nonneg (show 0 ≤ 5-F by linarith only [hFhi]) hx
  have h6 := mul_nonneg (show 0 ≤ u-35/3 by linarith only [hu]) hx
  nlinarith only [h1,h2,h3,h4,h5,h6]

theorem prefix_reference_C_bound (x y eps C : ℝ)
    (he : -1 ≤ eps) (hy : y ≤ 5*x/3)
    (hC : C=eps+x-2*y+1) : -C ≤ 7*x/3 := by
  linarith only [he,hy,hC]

theorem first_two_window_identity (x y a b eps : ℝ)
    (hc : y^2-x*y-x^2=eps) :
    ((y-1)+(x+y-a-1))^2-
      (x+(y-1))*((x+y-a-1)+(x+2*y-b-2))
    =eps+(b-a+1)*x+(b-3*a-2)*y+a^2+3*a+1-b := by
  nlinarith only [hc]

theorem first_two_window_all_padding (u x y eps : ℝ)
    (hu : 14 ≤ u) (hx : 1 ≤ x) (hy : 1 ≤ y) (he : -1 ≤ eps) :
    0 ≤ eps+(u+2)*x+(u-3)*y+3-u ∧
    0 ≤ eps+(u+3)*x+(u-2)*y+2-u ∧
    0 ≤ eps+(2*u+2)*x+(2*u-5)*y+8-2*u := by
  have h1 := mul_nonneg (show 0 ≤ u+2 by linarith only [hu])
    (show 0 ≤ x-1 by linarith only [hx])
  have h2 := mul_nonneg (show 0 ≤ u-3 by linarith only [hu])
    (show 0 ≤ y-1 by linarith only [hy])
  have h3 := mul_nonneg (show 0 ≤ u+3 by linarith only [hu])
    (show 0 ≤ x-1 by linarith only [hx])
  have h4 := mul_nonneg (show 0 ≤ u-2 by linarith only [hu])
    (show 0 ≤ y-1 by linarith only [hy])
  have h5 := mul_nonneg (show 0 ≤ 2*u+2 by linarith only [hu])
    (show 0 ≤ x-1 by linarith only [hx])
  have h6 := mul_nonneg (show 0 ≤ 2*u-5 by linarith only [hu])
    (show 0 ≤ y-1 by linarith only [hy])
  constructor
  · linarith only [he,h1,h2,hu]
  constructor <;> linarith only [he,h3,h4,h5,h6,hu]

theorem quaternary_kernel_positive (p T eps : ℝ)
    (hp0 : 0 ≤ p) (hp : p ≤ 13/8) (hT : 9 ≤ T) (he : -1 ≤ eps) :
    5/2 ≤ (5*(2-p)*T+(2+3*p)*eps)/4 := by
  have h1 := mul_nonneg (show 0 ≤ 2-p by linarith only [hp])
    (show 0 ≤ T-9 by linarith only [hT])
  have h2 := mul_nonneg (show 0 ≤ 2+3*p by linarith only [hp0])
    (show 0 ≤ eps+1 by linarith only [he])
  nlinarith only [h1,h2,hp]

theorem quaternary_odd_block (r p : ℝ) (hr : 1 ≤ r) (hp : p ≤ 13/8) :
    0 ≤ (r+1)*(2-2*p)+r*(22-12*p) := by
  have h1 := mul_nonneg (show 0 ≤ 14*r+2 by linarith only [hr])
    (show 0 ≤ 13/8-p by linarith only [hp])
  nlinarith only [h1,hr]

theorem quaternary_negative_atom_paid (p : ℝ) (hp : p ≤ 13/8) :
    27/16 ≤ (10-3*p)+(11/4)*(2-2*p) ∧
    2 < 4*(31-17*p) := by constructor <;> linarith only [hp]

theorem quaternary_pair_polynomial (w : ℝ) :
    (11*w-4)*(1+w)^8+4*(1+w)^4+5*w=
      100*w^3+340*w^4+546*w^5+504*w^6+276*w^7+84*w^8+11*w^9 := by ring

theorem quaternary_bottom_source (u p : ℝ) (hu : 8 ≤ u) (hp : p ≤ 13/8) :
    0 < u*(u-1)/2+2*u+4-p*(2*u+3) := by
  have h1 := mul_nonneg (show 0 ≤ 2*u+3 by linarith only [hu])
    (show 0 ≤ 13/8-p by linarith only [hp])
  nlinarith only [sq_nonneg (u-8),hu,h1]

theorem two_factor_atom_norm : (21/8:ℝ)*(27/40)^2 < 6/5 := by norm_num

theorem regular_geometry (u A B delta : ℝ)
    (hA : A ≤ B) (hB : B ≤ u-3) (hd : delta=A+B-2-u) :
    delta ≤ u-8 := by linarith only [hA,hB,hd]

theorem old_one_junction_scalar (u : ℝ) (hu : 16 ≤ u) :
    0 ≤ (u-2)*2*(u-1)-(3/2)*u*(u+1) := by
  nlinarith only [sq_nonneg (u-16),hu]

theorem old_one_junction_gap (u b B2 Bprev Bt D : ℝ)
    (hu : 16 ≤ u) (hb : 0 < b) (hbhi : b ≤ u+1)
    (hD : u-2 ≤ D) (hB : 2*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    3*u/2 ≤ b*Bprev-2*Bt := by
  have hF := old_one_junction_scalar u hu
  have hD0 : 0 ≤ D := by linarith only [hD,hu]
  have h1 := mul_nonneg (show 0 ≤ D-(u-2) by linarith only [hD])
    (show 0 ≤ 2*(u-1) by linarith only [hu])
  have h2 := mul_nonneg hD0 (show 0 ≤ Bprev-2*(u-1) by linarith only [hB])
  have h3 := mul_nonneg (show 0 ≤ 3*u/2 by linarith only [hu])
    (show 0 ≤ u+1-b by linarith only [hbhi])
  have hdefB := congrArg (fun z : ℝ => z*Bprev) hdef
  have hp : 0 ≤ b*((b*Bprev-2*Bt)-3*u/2) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  have hh := (mul_nonneg_iff_of_pos_left hb).mp hp
  linarith only [hh]

theorem regular_perturbed_junction (u gap err M : ℝ)
    (hu : 24 ≤ u) (hg : 3*u/2 ≤ gap)
    (he : err ≤ 6*u/5+2) (hm : 0 ≤ M) :
    0 < M+1+gap-err := by linarith only [hu,hg,he,hm]

theorem left_half_ULC_scalar (m : ℝ) (hm : 6 ≤ m) :
    (4*m+5)^2*(4*m+11/3) ≤ 16*(m+2)^2*(4*m+1) := by
  nlinarith only [sq_nonneg (m-6),hm]

theorem left_half_zero_row (m u q : ℝ) (hm : 6 ≤ m)
    (hu : u ≤ 4*m+3) (hq : q ≤ 2/3) :
    u+q+2 ≤ 4*(m+2)^2 := by
  nlinarith only [sq_nonneg (m-6),hm,hu,hq]

theorem left_atom_constants (p : ℝ) (hp : 8/5 ≤ p) (hphi : p ≤ 13/8) :
    48/5 ≤ 5*p+3 ∧ 2*p+1 ≤ 17/4 := by constructor <;> linarith only [hp,hphi]

theorem left_binomial_growth (m : ℝ) (hm : 6 ≤ m) :
    24*(m+2)*(3*m-1)*(3*m+1) ≤ 4*(4*m+1)*(4*m+2)*(4*m+3) := by
  have hx : 0 ≤ m-6 := by linarith only [hm]
  have hc : 0 ≤ (m-6)^3 := by positivity
  nlinarith only [hc,sq_nonneg (m-6),hx]

theorem left_budget_growth (m : ℝ) (hm : 6 ≤ m) :
    (17/4)*(m+3)^2 ≤ 6*(m+2)^2 := by
  nlinarith only [sq_nonneg (m-6),hm]

theorem left_binomial_base : (24137569:ℕ) < 128*Nat.choose 23 7 := by decide

theorem right_exponential_bases :
    (7:ℚ)*6 ≤ 11*(309/250)^7 ∧
    (8:ℚ)*7 ≤ 11*(309/250)^8 ∧
    (9:ℚ)*8 ≤ 11*(309/250)^9 ∧
    (10:ℚ)*9 ≤ 11*(309/250)^10 := by norm_num

theorem right_exponential_step (k q : ℝ) (hk : 10 ≤ k) (hq : 309/500 ≤ q) :
    k+1 ≤ 2*q*(k-1) := by
  have h1 := mul_nonneg (show 0 ≤ k-1 by linarith only [hk])
    (show 0 ≤ q-309/500 by linarith only [hq])
  nlinarith only [hk,h1]

theorem right_half_budget (u : ℝ) (hu : 24 ≤ u) :
    66*(u+2)^2*(u+2/3) ≤ 89*(u+1)*(u-1)*(u-2) := by
  have hx : 0 ≤ u-24 := by linarith only [hu]
  have hc : 0 ≤ (u-24)^3 := by positivity
  nlinarith only [hc,sq_nonneg (u-24),hx]

theorem right_half_zero_row (u q : ℝ) (hu : 24 ≤ u)
    (hq0 : 0 ≤ q) (_hq : q ≤ 2/3) :
    4*(u+1)*(u+q+2) ≤ (u+2)^2*(u+q) := by
  have h1 := mul_nonneg hq0 (show 0 ≤ u^2 by positivity)
  have hx : 0 ≤ u-24 := by linarith only [hu]
  have hc : 0 ≤ (u-24)^3 := by positivity
  nlinarith only [hc,sq_nonneg (u-24),hx,h1]

#print axioms transported_minor_term
#print axioms prefix_reference_loss_payment
#print axioms prefix_reference_C_bound
#print axioms first_two_window_identity
#print axioms first_two_window_all_padding
#print axioms quaternary_kernel_positive
#print axioms quaternary_odd_block
#print axioms quaternary_negative_atom_paid
#print axioms quaternary_pair_polynomial
#print axioms quaternary_bottom_source
#print axioms two_factor_atom_norm
#print axioms regular_geometry
#print axioms old_one_junction_scalar
#print axioms old_one_junction_gap
#print axioms regular_perturbed_junction
#print axioms left_half_ULC_scalar
#print axioms left_half_zero_row
#print axioms left_atom_constants
#print axioms left_binomial_growth
#print axioms left_budget_growth
#print axioms left_binomial_base
#print axioms right_exponential_bases
#print axioms right_exponential_step
#print axioms right_half_budget
#print axioms right_half_zero_row

end TwoFactorCompleteEntrance
