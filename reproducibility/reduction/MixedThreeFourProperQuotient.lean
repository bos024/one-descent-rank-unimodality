import Mathlib
set_option maxHeartbeats 4000000
namespace MixedThreeFourProperQuotient

theorem three_robust_head_polynomial_budgets (w : ℝ) (hw : 32 ≤ w) :
    let E2 := w*(w+1)/2
    let E3 := w*(w+1)*(w+2)/6
    let E4 := w*(w+1)*(w+2)*(w+3)/24
    let L1 := w-3/2
    let L2 := E2-w-3/2
    let L3 := E3-E2-2*w-1/4
    0≤L1 ∧ 0≤L2 ∧ 0≤L3 ∧
    0≤L1^2-(5/4)*E2 ∧
    0≤L2^2-(w+1/4)*E3 ∧
    0≤L3^2-E2*E4 := by
  dsimp
  let x := w-32
  have hx : 0≤x := by dsimp [x]; linarith
  have he : w=32+x := by dsimp [x]; ring
  rw [he]
  constructor
  · linarith
  · constructor
    · ring_nf; positivity
    · constructor
      · ring_nf; positivity
      · constructor
        · ring_nf; positivity
        · constructor <;> ring_nf <;> positivity

theorem robust_interval_minor_payment (x y z L U V : ℝ)
    (hx : 0≤x) (hL : 0≤L) (hy : L≤y) (hU : x≤U)
    (hV : z≤V) (hV0 : 0≤V) (hbudget : U*V≤L^2) :
    0≤y^2-x*z := by
  have h0 := mul_le_mul_of_nonneg_left hV hx
  have h1 := mul_le_mul_of_nonneg_right hU hV0
  have h2 : L^2≤y^2 := by nlinarith only [hy,hL]
  nlinarith only [h0,h1,h2,hbudget]

theorem exact_four_interval_quotient_correction (R : Type*) [CommRing R]
    (B J rem z l : R) (hB : (1-l*z)*B=1-z-z^2-z^3) :
    (1+z+z^2+z^3)*(B*J+rem)=
      B*((1+z+z^2+z^3)*J-(1-l*z)*rem)+2*rem := by
  linear_combination rem*hB

theorem four_remainder_norm_scale (a b x y : ℝ) :
    b*(2*x)^2-a*(2*x)*(2*y)+(2*y)^2=4*(b*x^2-a*x*y+y^2) := by ring

theorem whole_two_count_remainder_norm (N : ℕ → ℕ → ℝ) (b : ℝ)
    (hbase : N 0 0=b) (h3 : ∀ r,N (r+1) 0=b*N r 0)
    (h4 : ∀ r s,N r (s+1)=4*N r s) :
    ∀ r s,N r s=b^(r+1)*(4:ℝ)^s := by
  have hp : ∀ r,N r 0=b^(r+1) := by
    intro r
    induction r with
    | zero => simpa using hbase
    | succ r ih => rw [h3,ih]; ring
  intro r s
  induction s with
  | zero => simpa using hp r
  | succ s ih => rw [h4,ih]; ring

theorem entire_increasing_norm_target_induction (P : ℕ → Prop) (N : ℕ → ℝ)
    (c : ℝ) (hbase : P 0) (hN : ∀ s,N s≤N (s+1))
    (hstep : ∀ s,N (s+1)≤c → P s → P (s+1)) :
    ∀ s,N s≤c → P s := by
  intro s
  induction s with
  | zero => intro _; exact hbase
  | succ s ih =>
    intro h
    exact hstep s h (ih ((hN s).trans h))

theorem nonnegative_unit_mixture_bounds (a b x y : ℝ)
    (ha : 0≤a) (ha1 : a≤1) (hb : 0≤b) (hb1 : b≤1)
    (hx : 0≤x) (hy : 0≤y) : 0≤a*x+b*y ∧ a*x+b*y≤x+y := by
  have h0 := mul_nonneg ha hx
  have h1 := mul_nonneg hb hy
  have h2 := mul_le_mul_of_nonneg_right ha1 hx
  have h3 := mul_le_mul_of_nonneg_right hb1 hy
  constructor <;> nlinarith only [h0,h1,h2,h3]

theorem complete_forward_quotient_three_head_minors
    (a b R0 R1 w j0 j1 j2 j3 j4 E3 E4 : ℝ)
    (ha : 0≤a) (ha1 : a≤1) (hb : 0≤b) (hb1 : b≤1)
    (hR0 : -(1/4)≤R0 ∧ R0≤1/4) (hR1 : -(1/4)≤R1 ∧ R1≤1/4)
    (hw : 32 ≤ w) (hE3 : w*(w+1)*(w+2)/6-w≤E3 ∧ E3≤w*(w+1)*(w+2)/6)
    (hE4 : E4≤w*(w+1)*(w+2)*(w+3)/24)
    (h0 : j0=1-R0) (h1 : j1=w-a*j0-R1)
    (h2 : j2=w*(w+1)/2-a*j1-b*j0)
    (h3 : j3=E3-a*j2-b*j1) (h4 : j4=E4-a*j3-b*j2) :
    0<j0 ∧ 0<j1 ∧ 0<j2 ∧ 0≤j1^2-j0*j2 ∧
    0≤j2^2-j1*j3 ∧ 0≤j3^2-j2*j4 := by
  have budgets := three_robust_head_polynomial_budgets w hw
  dsimp at budgets
  have j0lo : 3/4≤j0 := by linarith [hR0.1,hR0.2]
  have j0hi : j0≤5/4 := by linarith [hR0.1,hR0.2]
  have j0pos : 0<j0 := by linarith
  have aj0pos := mul_nonneg ha j0pos.le
  have aj0le := mul_le_mul_of_nonneg_right ha1 j0pos.le
  have j1lo : w-3/2≤j1 := by linarith [hR1.2]
  have j1hi : j1≤w+1/4 := by linarith [hR1.1]
  have j1pos : 0<j1 := by linarith
  have mix1 := nonnegative_unit_mixture_bounds a b j1 j0 ha ha1 hb hb1 j1pos.le j0pos.le
  have j2lo : w*(w+1)/2-w-3/2≤j2 := by linarith [mix1.2]
  have j2hi : j2≤w*(w+1)/2 := by linarith [mix1.1]
  have L2pos : 0<w*(w+1)/2-w-3/2 := by nlinarith only [hw,sq_nonneg (w-1)]
  have j2pos : 0<j2 := by linarith
  have mix2 := nonnegative_unit_mixture_bounds a b j2 j1 ha ha1 hb hb1 j2pos.le j1pos.le
  have j3lo : w*(w+1)*(w+2)/6-w*(w+1)/2-2*w-1/4≤j3 := by
    linarith [mix2.2,hE3.1]
  have j3hi : j3≤w*(w+1)*(w+2)/6 := by linarith [mix2.1,hE3.2]
  have j3nonneg : 0≤j3 := by linarith [budgets.2.2.1]
  have mix3 := nonnegative_unit_mixture_bounds a b j3 j2 ha ha1 hb hb1 j3nonneg j2pos.le
  have j4hi : j4≤w*(w+1)*(w+2)*(w+3)/24 := by linarith [mix3.1]
  refine ⟨j0pos,j1pos,j2pos,?_,?_,?_⟩
  · apply robust_interval_minor_payment j0 j1 j2 (w-3/2) (5/4) (w*(w+1)/2)
      j0pos.le budgets.1 j1lo j0hi j2hi (by positivity)
    linarith [budgets.2.2.2.1]
  · apply robust_interval_minor_payment j1 j2 j3 (w*(w+1)/2-w-3/2)
      (w+1/4) (w*(w+1)*(w+2)/6) j1pos.le budgets.2.1 j2lo j1hi j3hi (by positivity)
    linarith [budgets.2.2.2.2.1]
  · apply robust_interval_minor_payment j2 j3 j4
      (w*(w+1)*(w+2)/6-w*(w+1)/2-2*w-1/4)
      (w*(w+1)/2) (w*(w+1)*(w+2)*(w+3)/24)
      j2pos.le budgets.2.2.1 j3lo j2hi j4hi (by positivity)
    linarith [budgets.2.2.2.2.2]

theorem entire_explicit_three_four_norm_cone (b : ℝ) (r s : ℕ)
    (hb : 1/2≤b) (hb6 : b≤6/11) (hs : 16 ≤ s) (hr : 3*s≤r+4) :
    32≤r ∧ b^(r+1)*(4:ℝ)^s≤1/64 := by
  have hb0 : 0≤b := by linarith
  have hb1 : b≤1 := by linarith
  have hp := pow_le_pow_of_le_one hb0 hb1 hr
  have hid : b^(r+4)=b^(r+1)*b^3 := by rw [show r+4=r+1+3 by omega,pow_add]
  rw [hid,pow_mul] at hp
  have hN : (b^(r+1)*(4:ℝ)^s)*b^3≤(4*b^3)^s := by
    have h := mul_le_mul_of_nonneg_right hp (show 0≤(4:ℝ)^s by positivity)
    rw [mul_pow]
    nlinarith only [h]
  have bmin : (1/8:ℝ)≤b^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hb 3
    norm_num at h
    exact h
  have qmax : 4*b^3≤(2/3:ℝ) := by
    have h := pow_le_pow_left₀ hb0 hb6 3
    nlinarith only [h]
  have qbound : (4*b^3)^s≤(2/3:ℝ)^16 := by
    apply le_trans (pow_le_pow_left₀ (by positivity) qmax s)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hmin := mul_le_mul_of_nonneg_left bmin (show 0≤b^(r+1)*(4:ℝ)^s by positivity)
  have hnum : (8:ℝ)*(2/3:ℝ)^16≤1/64 := by norm_num
  exact ⟨by omega,by nlinarith only [hN,hmin,qbound,hnum]⟩

#print axioms three_robust_head_polynomial_budgets
#print axioms robust_interval_minor_payment
#print axioms exact_four_interval_quotient_correction
#print axioms four_remainder_norm_scale
#print axioms whole_two_count_remainder_norm
#print axioms entire_increasing_norm_target_induction
#print axioms nonnegative_unit_mixture_bounds
#print axioms complete_forward_quotient_three_head_minors
#print axioms entire_explicit_three_four_norm_cone
end MixedThreeFourProperQuotient
