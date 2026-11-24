import Mathlib

set_option maxHeartbeats 0

namespace DividedCILaterPrimitive

theorem weighted_power_decay (q M : ℝ) (s : ℕ)
    (hq0 : 0 ≤ q) (hq : q ≤ 2/3) (hs : 2 ≤ s)
    (hbase : 2*((s:ℝ)+1)*q^s ≤ M) :
    ∀ k : ℕ, 2*(((s+k:ℕ):ℝ)+1)*q^(s+k) ≤ M := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hS : 2 ≤ ((s+k:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ s+k by omega)
    have hpos : 0 ≤ ((s+k:ℕ):ℝ)+2 := by linarith only [hS]
    have h1:=mul_nonneg (show 0 ≤ 2/3-q by linarith only [hq]) hpos
    have hfac : q*(((s+k:ℕ):ℝ)+2) ≤ ((s+k:ℕ):ℝ)+1 := by nlinarith only [h1,hS]
    have h2:=mul_nonneg (pow_nonneg hq0 (s+k))
      (show 0 ≤ ((s+k:ℕ):ℝ)+1-q*(((s+k:ℕ):ℝ)+2) by linarith only [hfac])
    have heq : 2*(((s+(k+1):ℕ):ℝ)+1)*q^(s+(k+1))
        =2*q^(s+k)*(q*(((s+k:ℕ):ℝ)+2)) := by
      rw [show s+(k+1)=(s+k)+1 by omega, pow_succ]
      push_cast
      ring
    change 2*(((s+(k+1):ℕ):ℝ)+1)*q^(s+(k+1)) ≤ M
    rw [heq]
    nlinarith only [h2,ih]

theorem double_quadratic_kernel_payment (u q : ℝ)
    (hu : 12 ≤ u) (hq : q ≤ 2/3) :
    (12/5)*(u+q) ≤ (u-1)*(u-2)/2 := by
  nlinarith only [sq_nonneg (u-12),hu,hq]

theorem double_last_head_payment (u q : ℝ)
    (hu : 12 ≤ u) (hq : q ≤ 5/8) :
    (7/8)*(u+q) ≤ u-q := by linarith only [hu,hq]

theorem double_row_zero_payments (u q : ℝ)
    (hu : 12 ≤ u) (hq0 : 0 ≤ q) (hq : q ≤ 2/3) :
    (2/5)*(3*u-3+2*q) ≤ (u-1)*(u-2)/2 ∧
    (1/4)*(3*u-3+2*q) ≤ u-q := by
  constructor
  · have h1:=double_quadratic_kernel_payment u q hu hq
    linarith only [h1,hu,hq0]
  · linarith only [hu,hq]

theorem nonempty_junction_scalar (u r : ℝ)
    (hu : 12 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-3) :
    0 ≤ (u-r-1)*(r+1)*(u-1)-u*(u+r) := by
  let S:=(u-5)/2
  let w:=r-1
  let F:=(u-r-1)*(r+1)*(u-1)-u*(u+r)
  let F1:=u^2-7*u+4
  let FR:=(u-1)*(u^2-6*u-1)/4
  have hS : 0 < S := by dsimp [S]; linarith only [hu]
  have hw : 0 ≤ w := by dsimp [w]; linarith only [hr]
  have hSw : 0 ≤ S-w := by dsimp [S,w]; linarith only [hrr]
  have hu1 : 0 ≤ u-1 := by linarith only [hu]
  have hF1 : 0 ≤ F1 := by
    dsimp [F1]
    nlinarith only [sq_nonneg (u-12),hu]
  have hFR : 0 ≤ FR := by
    have hpol : 0 ≤ u^2-6*u-1 := by nlinarith only [sq_nonneg (u-12),hu]
    dsimp [FR]; positivity
  have h1:=mul_nonneg hSw hF1
  have h2:=mul_nonneg hw hFR
  have h3 : 0 ≤ S*(u-1)*w*(S-w) := by positivity
  have heq : S*F=(S-w)*F1+w*FR+S*(u-1)*w*(S-w) := by dsimp [S,w,F,F1,FR]; ring
  have hprod : 0 ≤ S*F := by rw [heq]; linarith only [h1,h2,h3]
  exact nonneg_of_mul_nonneg_right hprod hS

theorem nonempty_interval_junction_gap (u r b B2 Bprev Bt D : ℝ)
    (hu : 12 ≤ u) (hr : 1 ≤ r) (hrr : 2*r ≤ u-3)
    (hb : 0 < b) (hbhi : b ≤ u+r)
    (hD : u-r-1 ≤ D) (hB : (r+1)*(u-1) ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    u ≤ b*Bprev-2*Bt := by
  have hF:=nonempty_junction_scalar u r hu hr hrr
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

theorem empty_interval_junction_gap (b B2 Bprev Bt D : ℝ)
    (hb : 0 < b) (hD : 0 ≤ D) (hB : b ≤ Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤ B2*Bprev) :
    D ≤ b*Bprev-2*Bt := by
  have h1:=mul_nonneg hD (show 0 ≤ Bprev-b by linarith only [hB])
  have hdefB:=congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤ b*((b*Bprev-2*Bt)-D) := by nlinarith only [h1,hdefB,hLC]
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg hb (show (b*Bprev-2*Bt)-D<0 by linarith only [hbad])
  linarith only [hpay,hneg]

#print axioms weighted_power_decay
#print axioms double_quadratic_kernel_payment
#print axioms double_last_head_payment
#print axioms double_row_zero_payments
#print axioms nonempty_junction_scalar
#print axioms nonempty_interval_junction_gap
#print axioms empty_interval_junction_gap

end DividedCILaterPrimitive
