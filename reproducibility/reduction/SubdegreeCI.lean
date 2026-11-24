import Mathlib

set_option maxHeartbeats 0

namespace SubdegreeCI

theorem relaxed_fourfold_row_zero (u q : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3) :
    (2/5)*(6*u+2+4*q) ≤ (u-1)*(u-2)/2 ∧
    (6*u+2+4*q)/16 ≤ u-q ∧ 6*u+2+4*q ≤ u*(u+1) := by
  refine ⟨?_,?_,?_⟩
  · nlinarith only [sq_nonneg (u-16),hu,hq]
  · linarith only [hu,hq]
  · nlinarith only [sq_nonneg (u-16),hu,hq]

theorem inverse_initial_minor_identity (q p x b0 b1 : ℝ)
    (hpq : p*q=1) :
    x^2-(q*(x+b0))*(p*x-b1)=x*(q*b1-b0)+q*b0*b1 := by
  linear_combination -(x^2+b0*x)*hpq

theorem inverse_initial_minor_payment (q x b0 b1 : ℝ)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (hgap : b0 ≤ q*b1) :
    0 ≤ x*(q*b1-b0)+q*b0*b1 := by positivity

theorem inverse_strict_initial_budget (u q b0 b1 : ℝ)
    (hu : 16 ≤ u) (hq : 3/5 ≤ q) (hb0 : b0 ≤ 2) (hb1 : u ≤ b1) :
    b0 < q*b1 := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hu0 : 0 ≤ u := by linarith only [hu]
  have h1:=mul_le_mul_of_nonneg_left hb1 hq0
  have h2:=mul_le_mul_of_nonneg_right hq hu0
  nlinarith only [h1,h2,hu,hb0]

theorem subdegree_junction_scalar (u r : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-1) :
    0 ≤ (u-r-1)*(r+1)*(u-1)-u*(u+r) := by
  let S:=(u-3)/2
  let w:=r-1
  let F:=(u-r-1)*(r+1)*(u-1)-u*(u+r)
  let F1:=u^2-7*u+4
  let FR:=(u^3-7*u^2+u+1)/4
  have hS : 0 < S := by dsimp [S]; linarith only [hu]
  have hw : 0 ≤ w := by dsimp [w]; linarith only [hr]
  have hSw : 0 ≤ S-w := by dsimp [S,w]; linarith only [hrr]
  have hu1 : 0 ≤ u-1 := by linarith only [hu]
  have hF1 : 0 ≤ F1 := by dsimp [F1]; nlinarith only [sq_nonneg (u-16),hu]
  have hFR : 0 ≤ FR := by
    have hpol : 0 ≤ u^2-7*u := by nlinarith only [sq_nonneg (u-16),hu]
    have hu0 : 0 ≤ u := by linarith only [hu]
    have hp:=mul_nonneg hu0 hpol
    dsimp [FR]
    nlinarith only [hp,hu]
  have h1:=mul_nonneg hSw hF1
  have h2:=mul_nonneg hw hFR
  have h3 : 0 ≤ S*(u-1)*w*(S-w) := by positivity
  have heq : S*F=(S-w)*F1+w*FR+S*(u-1)*w*(S-w) := by
    dsimp [S,w,F,F1,FR]; ring
  have hprod : 0 ≤ S*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hS

theorem subdegree_interval_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-1)
    (hb : 0 < b) (hbhi : b ≤ u+r)
    (hD : u-r-1 ≤ D) (hB : (r+1)*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    u ≤ b*Bprev-2*Bt := by
  have hF:=subdegree_junction_scalar u r hu hr hrr
  have hDlo : 0 ≤ u-r-1 := by linarith only [hu,hrr]
  have hD0 : 0 ≤ D := by linarith only [hD,hDlo]
  have hB0 : 0 ≤ (r+1)*(u-1) := by
    have hr1 : 0 ≤ r+1 := by linarith only [hr]
    have hu1 : 0 ≤ u-1 := by linarith only [hu]
    positivity
  have h1:=mul_nonneg (show 0 ≤ D-(u-r-1) by linarith only [hD]) hB0
  have h2:=mul_nonneg hD0 (show 0 ≤ Bprev-(r+1)*(u-1) by linarith only [hB])
  have h3:=mul_nonneg (show 0 ≤ u by linarith only [hu])
    (show 0 ≤ u+r-b by linarith only [hbhi])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-u) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg hb (show (b*Bprev-2*Bt)-u<0 by linarith only [hbad])
  linarith only [hpay,hneg]

theorem golden_seventh_power_bound (q : ℝ) (hroot : q^2+q=1)
    (hqlo : 3/5 ≤ q) : q^5 < 1/10 ∧ q^7 ≤ 1/25 := by
  have hq0 : 0 ≤ q := by linarith only [hqlo]
  have hq : q < 31/50 := by
    by_contra hn
    have h1:=mul_nonneg (show 0 ≤ q-31/50 by linarith only [hn])
      (show 0 ≤ q+31/50+1 by linarith only [hq0])
    nlinarith only [h1,hroot]
  have hq5 : q^5=5*q-3 := by
    linear_combination (q^3-q^2+2*q-3)*hroot
  have h5 : q^5 < 1/10 := by linarith only [hq5,hq]
  have h2 : q^2 ≤ 2/5 := by linarith only [hroot,hqlo]
  have hp:=mul_le_mul (le_of_lt h5) h2 (sq_nonneg q) (by norm_num : (0:ℝ) ≤ 1/10)
  constructor
  · exact h5
  · convert hp using 1 <;> ring

theorem subdegree_uniform_atom_payment (u : ℝ) (hu : 16 ≤ u) :
    (16/25)*(3*u/2+1/6) ≤ 39*u/40 := by linarith only [hu]

theorem exceptional_endpoint_negative (u q z : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3)
    (hzlo : -(1/4) ≤ z) (hzhi : z ≤ 1) :
    -u+2*q*(1-z)<0 := by
  have h1:=mul_le_mul hq (show 1-z ≤ 5/4 by linarith only [hzlo])
    (show 0 ≤ 1-z by linarith only [hzhi]) (by norm_num : (0:ℝ) ≤ 2/3)
  nlinarith only [h1,hu]

theorem actual_boundary_unit_alignment (q p x b prev modelprev : ℝ)
    (hpq : p*q=1) (hprev : prev=q*(x+b-p))
    (hmodel : modelprev=q*(x+b)) : modelprev=prev+1 := by
  nlinarith only [hpq,hprev,hmodel]

theorem subdegree_positive_Cassini_seed (a b delta A : ℝ)
    (hA : 0 < A) (ha : 0 ≤ a) (hdelta : 0 ≤ delta)
    (hCass : b^2+a*b-a^2=A) :
    b*(a+b)-(a-delta)*a=A+delta*a ∧
    0 < b*(a+b)-(a-delta)*a := by
  have heq : b*(a+b)-(a-delta)*a=A+delta*a := by nlinarith only [hCass]
  have hp:=mul_nonneg hdelta ha
  exact ⟨heq,by linarith only [heq,hp,hA]⟩

#print axioms relaxed_fourfold_row_zero
#print axioms inverse_initial_minor_identity
#print axioms inverse_initial_minor_payment
#print axioms inverse_strict_initial_budget
#print axioms subdegree_junction_scalar
#print axioms subdegree_interval_junction_gap
#print axioms golden_seventh_power_bound
#print axioms subdegree_uniform_atom_payment
#print axioms exceptional_endpoint_negative
#print axioms actual_boundary_unit_alignment
#print axioms subdegree_positive_Cassini_seed

end SubdegreeCI
