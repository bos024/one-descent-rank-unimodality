import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
namespace FourSubdegreeCEntrance

theorem differential_product_identity (z A Ap B Bp m n : ℝ) :
    (1+z)*(Ap*B+A*Bp)-(m+n)*A*B=
      B*((1+z)*Ap-m*A)+A*((1+z)*Bp-n*B) := by ring

theorem interval_differential_coefficients (t n : ℝ) (ht : 2 ≤ t) (hn : 0 ≤ n) :
    0 ≤ 2*n ∧ 0 ≤ t-2 := by constructor <;> linarith only [ht,hn]

theorem loss_growth_seed_cone (w a l b c : ℝ)
    (hw : 11 ≤ w) (ha : 1 ≤ a) (haa : a ≤ 2)
    (hl : w*a ≤ l) (hlhi : l ≤ 2*w+1)
    (hb : (w-1)*l ≤ 2*b) (hc : (w-2)*b ≤ 3*c) :
    a+1 ≤ a+l ∧ 2*(a+l) ≤ b ∧ 2*(a+1)+3 ≤ b ∧
    3*b ≤ c ∧ a+l ≤ 2*w+3 := by
  have h1 := mul_nonneg (show 0 ≤ w-11 by linarith only [hw])
    (show 0 ≤ a by linarith only [ha])
  have hl11 : 11*a ≤ l := by nlinarith only [h1,hl]
  have hl0 : 0 ≤ l := by linarith only [ha,hl11]
  have h2 := mul_nonneg (show 0 ≤ w-11 by linarith only [hw]) hl0
  have hb5 : 5*l ≤ b := by nlinarith only [h2,hb]
  have hb0 : 0 ≤ b := by linarith only [hl0,hb5]
  have h3 := mul_nonneg (show 0 ≤ w-11 by linarith only [hw]) hb0
  have hcb : 3*b ≤ c := by nlinarith only [h3,hc]
  constructor
  · linarith only [ha,hl11]
  constructor
  · linarith only [ha,hl11,hb5]
  constructor
  · linarith only [ha,hl11,hb5]
  constructor
  · exact hcb
  · linarith only [haa,hlhi]

theorem homogeneous_reference_ratio (q t x y : ℝ)
    (hq0 : 0 ≤ q) (hq : q^2+q=1) (ht : t ≤ 5-8*q)
    (ht0 : 0 ≤ t) (hx : 0 < x)
    (hdef : y*(1+t)=x*(1+q-q*t)) :
    3*x/2 ≤ y := by
  have h1 := mul_nonneg (show 0 ≤ q+3/2 by linarith only [hq0])
    (show 0 ≤ 5-8*q-t by linarith only [ht])
  have hg : 0 ≤ 1+q-q*t-(3/2)*(1+t) := by nlinarith only [h1,hq]
  have h2 := mul_nonneg (le_of_lt hx) hg
  have hp : 0 ≤ (1+t)*(y-3*x/2) := by nlinarith only [h2,hdef]
  have hden : 0 < 1+t := by linarith only [ht0]
  have hh := (mul_nonneg_iff_of_pos_left hden).mp hp
  linarith only [hh]

theorem earliest_ordinary_seed_identity (x y e b c : ℝ) :
    (x-e)*(x-b)-(y-x+1)*(y-c)=
      x^2+x*y-y^2+y*(c-1)-x*(c+b+e)+c+e*b := by ring

theorem earliest_ordinary_seed_paid (x y e b c A L : ℝ)
    (hx : 0 ≤ x) (hy : 3*x/2 ≤ y) (he : 0 ≤ e)
    (hb : 2*e+3 ≤ b) (hc : 3*b ≤ c) (hA : 0 < A)
    (hAd : A=x^2+x*y-y^2) (hL : L ≤ y-x+1) (hD : 0 ≤ y-c) :
    0 < (x-e)*(x-b)-L*(y-c) := by
  have hc1 : 0 ≤ c-1 := by linarith only [hb,hc,he]
  have h1 := mul_nonneg (show 0 ≤ y-3*x/2 by linarith only [hy]) hc1
  have h2 := mul_nonneg hx (show 0 ≤ c/2-b-e-3/2 by linarith only [hc,hb])
  have h3 := mul_nonneg he (show 0 ≤ b by linarith only [hb,he])
  have h4 := mul_nonneg (show 0 ≤ y-x+1-L by linarith only [hL]) hD
  have hid := earliest_ordinary_seed_identity x y e b c
  nlinarith only [h1,h2,h3,h4,hid,hAd,hA,hc1]

theorem middle_ordinary_seed_identity (x y e S b c : ℝ) :
    (y-S)*(x-b)-(x-e)*(y-c)=x*(c-S)-y*(b-e)+S*b-e*c := by ring

theorem middle_ordinary_seed_paid (x y e S b c : ℝ)
    (he : 0 ≤ e) (hx : 2*e ≤ x) (hy : y ≤ 2*x)
    (hS : e ≤ S) (hb : 2*S ≤ b) (hc : 3*b ≤ c) :
    2*e^2 ≤ x*(c-S)-y*(b-e)+S*b-e*c := by
  have hbe : 2*e ≤ b := by linarith only [hS,hb]
  have ht : 0 ≤ c-S-2*b+2*e := by linarith only [hc,hb,hS,he]
  have h1 := mul_nonneg (show 0 ≤ 2*x-y by linarith only [hy])
    (show 0 ≤ b-e by linarith only [hbe,he])
  have h2 := mul_nonneg (show 0 ≤ x-2*e by linarith only [hx]) ht
  have h3 := mul_nonneg (show 0 ≤ S-e by linarith only [hS])
    (show 0 ≤ b-2*e by linarith only [hbe])
  have h4 := mul_nonneg he (show 0 ≤ c-3*b by linarith only [hc])
  nlinarith only [h1,h2,h3,h4]

theorem last_ordinary_seed_paid (x y S b c A : ℝ)
    (hS : 0 ≤ S) (hx : S ≤ x) (hy : x ≤ y)
    (hb : 2*S ≤ b) (hc : 3*b ≤ c) (hA : 0 < A) :
    0 < A-x*(S+2*b)+y*(S-b+c)+b^2+S*b-S*c := by
  have h1 := mul_nonneg (show 0 ≤ y-x by linarith only [hy])
    (show 0 ≤ S-b+c by linarith only [hS,hb,hc])
  have h2 := mul_nonneg (show 0 ≤ x-S by linarith only [hx])
    (show 0 ≤ c-3*b by linarith only [hc])
  have h3 := mul_nonneg (show 0 ≤ b by linarith only [hS,hb])
    (show 0 ≤ b-2*S by linarith only [hb])
  nlinarith only [h1,h2,h3,hA]

#print axioms differential_product_identity
#print axioms interval_differential_coefficients
#print axioms loss_growth_seed_cone
#print axioms homogeneous_reference_ratio
#print axioms earliest_ordinary_seed_identity
#print axioms earliest_ordinary_seed_paid
#print axioms middle_ordinary_seed_identity
#print axioms middle_ordinary_seed_paid
#print axioms last_ordinary_seed_paid
end FourSubdegreeCEntrance
