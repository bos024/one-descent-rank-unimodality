import Mathlib

set_option maxHeartbeats 0

namespace DegreeBoundaryCI

theorem quadratic_geometric_decay (q : ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ 2/3) (hpow : q^15 ≤ 1/1024) :
    ∀ k : ℕ, (((k:ℝ)+16)*((k:ℝ)+17))*q^(k+15) ≤ 1/3 := by
  intro k
  induction k with
  | zero => norm_num; nlinarith only [hpow]
  | succ k ih =>
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have h1:=mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq])
      (show 0 ≤ (k:ℝ)+18 by linarith only [hk])
    have hf : q*((k:ℝ)+18) ≤ (k:ℝ)+16 := by nlinarith only [h1,hk]
    have h2:=mul_nonneg (show 0 ≤ (k:ℝ)+17 by linarith only [hk])
      (show 0 ≤ (k:ℝ)+16-q*((k:ℝ)+18) by linarith only [hf])
    have h3:=mul_nonneg (pow_nonneg hq0 (k+15)) h2
    have heq : ((((k+1:ℕ):ℝ)+16)*(((k+1:ℕ):ℝ)+17))*q^(k+1+15)
        =q^(k+15)*(((k:ℝ)+17)*(q*((k:ℝ)+18))) := by
      rw [show k+1+15=(k+15)+1 by omega,pow_succ]
      push_cast
      ring
    rw [heq]
    nlinarith only [h3,ih]

theorem quadruple_interior_payment (u q : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3) :
    (24/5)*(u+q) ≤ (u-1)*(u-2)/2 := by
  nlinarith only [sq_nonneg (u-16),hu,hq]

theorem quadruple_row_zero_payments (u q : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3) :
    (2/5)*(6*u+4*q) ≤ (u-1)*(u-2)/2 ∧
    (6*u+4*q)/16 ≤ u-q ∧ 6*u+4*q ≤ u*(u+1) := by
  refine ⟨?_,?_,?_⟩
  · nlinarith only [sq_nonneg (u-16),hu,hq]
  · linarith only [hu,hq]
  · nlinarith only [sq_nonneg (u-16),hu,hq]

theorem quadruple_penultimate_payment (u q : ℝ)
    (hu : 16 ≤ u) (hq : q ≤ 2/3) :
    (11/25)*(u+q) ≤ u-q := by linarith only [hu,hq]

theorem boundary_first_ordinary_minor (w c q E2 : ℝ)
    (hw : 3 ≤ w) (hc0 : 0 ≤ c)
    (hq0 : 0 ≤ q) (hq : q ≤ 2/3)
    (hE0 : 0 ≤ E2) (hE : E2 ≤ w^2/2) :
    0 < w^2-(1-c)*(E2+q*w) := by
  have hw0 : 0 ≤ w := by linarith only [hw]
  have h1:=mul_nonneg hc0 (show 0 ≤ E2+q*w by positivity)
  have h2:=mul_nonneg hw0 (show 0 ≤ 2/3-q by linarith only [hq])
  nlinarith only [h1,h2,hE,sq_nonneg (w-3),hw]

theorem boundary_junction_scalar (u r : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-2) :
    0 ≤ (u-r-1)*(r+1)*(u-1)-u*(u+r) := by
  let S:=(u-4)/2
  let w:=r-1
  let F:=(u-r-1)*(r+1)*(u-1)-u*(u+r)
  let F1:=u^2-7*u+4
  let FR:=u*(u^2-7*u+4)/4
  have hS : 0 < S := by dsimp [S]; linarith only [hu]
  have hw : 0 ≤ w := by dsimp [w]; linarith only [hr]
  have hSw : 0 ≤ S-w := by dsimp [S,w]; linarith only [hrr]
  have hu1 : 0 ≤ u-1 := by linarith only [hu]
  have hpol : 0 ≤ u^2-7*u+4 := by nlinarith only [sq_nonneg (u-16),hu]
  have hF1 : 0 ≤ F1 := by exact hpol
  have hFR : 0 ≤ FR := by dsimp [FR]; positivity
  have h1:=mul_nonneg hSw hF1
  have h2:=mul_nonneg hw hFR
  have h3 : 0 ≤ S*(u-1)*w*(S-w) := by positivity
  have heq : S*F=(S-w)*F1+w*FR+S*(u-1)*w*(S-w) := by
    dsimp [S,w,F,F1,FR]; ring
  have hprod : 0 ≤ S*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hS

theorem boundary_interval_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 16 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-2)
    (hb : 0 < b) (hbhi : b ≤ u+r)
    (hD : u-r-1 ≤ D) (hB : (r+1)*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    u ≤ b*Bprev-2*Bt := by
  have hF:=boundary_junction_scalar u r hu hr hrr
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

theorem boundary_perturbed_junction (u gap err M : ℝ)
    (hgap : u ≤ gap) (herr : err ≤ 24*u/25)
    (hM : 0 ≤ M) :
    u/25 ≤ gap-err ∧ 1+u/25 ≤ M+1+gap-err := by
  constructor <;> linarith only [hgap,herr,hM]

theorem single_last_primitive_identity (p u z : ℝ) :
    (p+p^2*z)^2-(p*u-p^2-p^3*z)*(-p*z)=p^2*(1+(u+p)*z) := by
  ring

theorem lower_previous_boundary_preserves_LC (prev cur next modelprev : ℝ)
    (hn : 0 ≤ next) (hp : prev ≤ modelprev)
    (hLC : 0 ≤ cur^2-modelprev*next) :
    0 ≤ cur^2-prev*next := by
  have h1:=mul_nonneg hn (show 0 ≤ modelprev-prev by linarith only [hp])
  nlinarith only [h1,hLC]

theorem subgolden_entrance_and_one_seed (p c b d delta A : ℝ)
    (hc : c < delta) (hgold : d-p*b=c)
    (hCass : b^2+b*d-d^2 = -A) (hd : A ≤ d)
    (hd0 : 0 ≤ d) (hdelta : 1 ≤ delta) :
    d-delta < p*b ∧ 0 ≤ b*(b+d)-d*(d-delta) := by
  have h1:=mul_nonneg hd0 (show 0 ≤ delta-1 by linarith only [hdelta])
  constructor <;> nlinarith only [hc,hgold,hCass,hd,h1]

#print axioms quadratic_geometric_decay
#print axioms quadruple_interior_payment
#print axioms quadruple_row_zero_payments
#print axioms quadruple_penultimate_payment
#print axioms boundary_first_ordinary_minor
#print axioms boundary_junction_scalar
#print axioms boundary_interval_junction_gap
#print axioms boundary_perturbed_junction
#print axioms single_last_primitive_identity
#print axioms lower_previous_boundary_preserves_LC
#print axioms subgolden_entrance_and_one_seed

end DegreeBoundaryCI
