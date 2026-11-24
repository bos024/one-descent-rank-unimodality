import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace ThreeFactorEarlierCut

theorem ternary_base_positive (p : ℝ) (hp : p ≤13/8) :
    ∀ k : ℕ, 1/8 ≤ 2^(k+2)*(5-3*p)-(2-p) := by
  intro k
  induction k with
  | zero => norm_num; linarith only [hp]
  | succ k ih =>
    have ha : 0 ≤5-3*p := by linarith only [hp]
    have hpow : 0 ≤(2:ℝ)^(k+2) := by positivity
    have hb := mul_nonneg hpow ha
    rw [show k+1+2=(k+2)+1 by omega,pow_succ]
    nlinarith only [ih,hb]

theorem even_kernel_block (m p : ℝ) (hm : 0 ≤ m) (hp : p ≤13/8) :
    1+7*m/8 ≤ (m+1)+m*(8-5*p) := by
  have hh := mul_nonneg hm (show 0 ≤13/8-p by linarith only [hp])
  nlinarith only [hh]

theorem odd_kernel_block (m p : ℝ) (hm : 2 ≤ m) (hp : p ≤13/8) :
    9/8 ≤ m*(99-60*p)-75+45*p := by
  have h1 := mul_nonneg (show 0 ≤60*m-45 by linarith only [hm])
    (show 0 ≤13/8-p by linarith only [hp])
  nlinarith only [h1,hm]

theorem ternary_negative_atoms_paid (p : ℝ) (hp : p ≤13/8) :
    9/8 ≤ (10-5*p)+3*(3-2*p) ∧
    0 ≤ (57-33*p)+9*(24-15*p) ∧
    3 < 6*(19-11*p)+(24-15*p) ∧
    3 < 6*(19-11*p) := by
  constructor
  · linarith only [hp]
  constructor
  · linarith only [hp]
  constructor <;> linarith only [hp]

theorem ternary_first_pair_identity (w : ℝ) :
    (3*w-1)*(1+w)^3+1=6*w^2+8*w^3+3*w^4 := by ring

theorem ternary_third_pair_identity (w : ℝ) :
    (9*w-1)*(1+w)^9+1=
      45*w^2+240*w^3+630*w^4+1008*w^5+1050*w^6+
      720*w^7+315*w^8+80*w^9+9*w^10 := by ring

theorem bottom_source_row (u p : ℝ) (hu : 6 ≤u) (hp : p ≤13/8) :
    0 < u*(u-1)/2+3*u+7-p*(2*u+5) := by
  have h1 := mul_nonneg (show 0 ≤2*u+5 by linarith only [hu])
    (show 0 ≤13/8-p by linarith only [hp])
  nlinarith only [sq_nonneg (u-6),hu,h1]

theorem penultimate_read_lower (u p eps : ℝ) (hu : 14 ≤u)
    (hp : 8/5 ≤p) (hphi2 : p^2 ≤8/3) (he : 0 ≤eps) :
    7*u/5 ≤p*u-p^2+eps := by
  have h1 := mul_nonneg (show 0 ≤u by linarith only [hu])
    (show 0 ≤p-8/5 by linarith only [hp])
  nlinarith only [h1,hu,hphi2,he]

theorem penultimate_unit_payments (u q : ℝ) (hu : 14 ≤u) (hq : q ≤2/3) :
    u/2+2 ≤(7*u/5)*(2/3) ∧
    u/5+29/15 ≤(7*u/5)*(1/3) ∧
    u+q+2 ≤7*u/5 := by
  constructor
  · linarith only [hu]
  constructor <;> linarith only [hu,hq]

theorem three_factor_norm : (21/8:ℝ)*(27/40)^3 <5/6 := by norm_num

theorem old_two_junction_scalar (u : ℝ) (hu : 12 ≤u) :
    0 ≤ (u-3)*3*(u-1)-(3/2)*u*(u+2) := by
  nlinarith only [sq_nonneg (u-12),hu]

theorem old_two_junction_gap (u b B2 Bprev Bt D : ℝ)
    (hu : 12 ≤u) (hb : 0 <b) (hbhi : b ≤u+2)
    (hD : u-3 ≤D) (hB : 3*(u-1) ≤Bprev)
    (hdef : D=b^2-2*B2) (hLC : b*Bt ≤B2*Bprev) :
    3*u/2 ≤b*Bprev-2*Bt := by
  have hF := old_two_junction_scalar u hu
  have hD0 : 0 ≤D := by linarith only [hD,hu]
  have h1 := mul_nonneg (show 0 ≤D-(u-3) by linarith only [hD])
    (show 0 ≤3*(u-1) by linarith only [hu])
  have h2 := mul_nonneg hD0 (show 0 ≤Bprev-3*(u-1) by linarith only [hB])
  have h3 := mul_nonneg (show 0 ≤3*u/2 by linarith only [hu])
    (show 0 ≤u+2-b by linarith only [hbhi])
  have hdefB := congrArg (fun z : ℝ => z*Bprev) hdef
  have hpay : 0 ≤b*((b*Bprev-2*Bt)-3*u/2) := by
    nlinarith only [hF,h1,h2,h3,hLC,hdefB]
  have hh := (mul_nonneg_iff_of_pos_left hb).mp hpay
  linarith only [hh]

theorem three_factor_perturbed_junction (u gap err M : ℝ)
    (hu : 14 ≤u) (hg : 3*u/2 ≤gap)
    (he : err ≤5*u/6+20/9) (hm : 0 ≤M) :
    0 < M+1+gap-err := by linarith only [hu,hg,he,hm]

theorem earlier_kernel_scalar (m : ℝ) (hm : 4 ≤ m) :
    (3*m+4)^2*(3*m+8/3) ≤12*(m+2)^2*(3*m+1) := by
  have hx : 0 ≤ m-4 := by linarith only [hm]
  have hc : 0 ≤(m-4)^3 := by positivity
  nlinarith only [hc,sq_nonneg (m-4),hx]

theorem earlier_zero_row (u m q : ℝ) (hm : 4 ≤ m)
    (hu : u ≤3*m+2) (hq : q ≤2/3) :
    u+q+3 ≤3*(m+2)^2 := by
  nlinarith only [sq_nonneg (m-4),hm,hu,hq]

theorem binomial_growth_payment (m : ℝ) (hm : 5 ≤ m) :
    8*(m+2)*(2*m-1) ≤3*(3*m+1)*(3*m+2) ∧
    2*(m+3)^2 ≤3*(m+2)^2 := by
  constructor <;> nlinarith only [sq_nonneg (m-5),hm]

theorem earlier_read_payment (H v Q : ℝ) (hH : 0 <H)
    (hv : 1 <v) (hQ : H*v ≤Q) : 0 < Q-H := by
  have hh := mul_pos hH (show 0 <v-1 by linarith only [hv])
  nlinarith only [hh,hQ]

#print axioms ternary_base_positive
#print axioms even_kernel_block
#print axioms odd_kernel_block
#print axioms ternary_negative_atoms_paid
#print axioms ternary_first_pair_identity
#print axioms ternary_third_pair_identity
#print axioms bottom_source_row
#print axioms penultimate_read_lower
#print axioms penultimate_unit_payments
#print axioms three_factor_norm
#print axioms old_two_junction_scalar
#print axioms old_two_junction_gap
#print axioms three_factor_perturbed_junction
#print axioms earlier_kernel_scalar
#print axioms earlier_zero_row
#print axioms binomial_growth_payment
#print axioms earlier_read_payment

end ThreeFactorEarlierCut
