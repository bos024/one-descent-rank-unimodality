import FixedTerminalFourteenSlope
import ActualDyadicSourcePayment
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FixedTerminalElevenDensity
open ActualDyadicSlopeNorm
noncomputable section
def shortRatio : ℝ := 175/192
def relative (t : ℕ) : ℝ := FixedTerminalFourteenSlope.relative t
def kernelPoly (x : ℝ) : ℝ := (x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6)/720
def kernelBound : ℝ := 3003*rho^8

theorem whole_short_source_polynomial_budget (m : ℕ) (hm : 34 ≤ m) :
    100*(m:ℝ)^5 ≤ (2:ℝ)^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hmR : (34:ℝ) ≤ m := by exact_mod_cast hm
    have hratio : (m:ℝ)+1 ≤ (35/34:ℝ)*(m:ℝ) := by nlinarith
    have hp := pow_le_pow_left₀ (show 0 ≤ (m:ℝ)+1 by positivity) hratio 5
    have hconstant : (35/34:ℝ)^5 ≤ 2 := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hconstant (show (0:ℝ) ≤ (m:ℝ)^5 by positivity)
    rw [mul_pow] at hp
    push_cast
    have htwo : (2:ℝ)^(m+1)=(2:ℝ)^m*2 := pow_succ _ _
    rw [htwo]
    nlinarith

private theorem all_kernel_poly_nonnegative (i : ℕ) : 0 ≤ kernelPoly (i:ℝ) := by
  dsimp [kernelPoly]
  positivity

private theorem all_kernel_weighted_point (i : ℕ) : kernelPoly (i:ℝ)*rho^i ≤ kernelBound := by
  by_cases hsmall : i ≤ 8
  · interval_cases i <;> norm_num [kernelPoly,kernelBound,rho]
  · have hi8 : 8 ≤ i := by omega
    clear hsmall
    induction i, hi8 using Nat.le_induction with
    | base => norm_num [kernelPoly,kernelBound,rho]
    | succ i hi ih =>
      have hiR : (8:ℝ) ≤ i := by exact_mod_cast hi
      have hf : rho*((i:ℝ)+7) ≤ (i:ℝ)+1 := by norm_num [rho]; nlinarith
      have hrec : ((i:ℝ)+1)*kernelPoly ((i:ℝ)+1)=((i:ℝ)+7)*kernelPoly (i:ℝ) := by
        dsimp [kernelPoly]
        ring_nf
      have hp0 : 0 ≤ kernelPoly (i:ℝ)*rho^i :=
        mul_nonneg (all_kernel_poly_nonnegative i) (pow_nonneg (by norm_num [rho]) _)
      have hm := mul_le_mul_of_nonneg_right hf hp0
      have heq := congrArg (fun z : ℝ => z*rho^(i+1)) hrec
      rw [pow_succ] at heq
      have hstep : ((i:ℝ)+1)*(kernelPoly ((i:ℝ)+1)*rho^(i+1)) ≤
          ((i:ℝ)+1)*(kernelPoly (i:ℝ)*rho^i) := by
        rw [pow_succ]
        nlinarith
      have hcancel := (mul_le_mul_iff_right₀ (show (0:ℝ) < (i:ℝ)+1 by positivity)).mp hstep
      push_cast
      exact hcancel.trans ih

theorem whole_seven_interval_weighted_coefficients (kernel : ℕ → ℝ)
    (hk : ∀ i, kernel i ≤ kernelPoly (i:ℝ)) (i : ℕ) :
    kernel i*rho^i ≤ kernelBound := by
  have h := mul_le_mul_of_nonneg_right (hk i) (pow_nonneg (show 0 ≤ rho by norm_num [rho]) i)
  exact h.trans (all_kernel_weighted_point i)

theorem whole_weighted_convolution_general_constant (kernel G : ℕ → ℝ)
    (n : ℕ) (C mass : ℝ) (hC : 0 ≤ C) (hG : ∀ i, 0 ≤ G i)
    (hk : ∀ i ≤ n, kernel i*rho^i ≤ C)
    (hMass : (∑ j ∈ Finset.range (n+1), G j*rho^j) ≤ mass) :
    rho^n*(∑ i ∈ Finset.range (n+1), kernel i*G (n-i)) ≤ C*mass := by
  have hterm : ∀ i ∈ Finset.range (n+1),
      kernel i*G (n-i)*rho^n ≤ C*(G (n-i)*rho^(n-i)) := by
    intro i hi
    have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
    have he : i+(n-i)=n := by omega
    have hp := pow_add rho i (n-i)
    rw [he] at hp
    have hm := mul_le_mul_of_nonneg_right (hk i hin)
      (show 0 ≤ G (n-i)*rho^(n-i) by
        exact mul_nonneg (hG (n-i)) (pow_nonneg (by norm_num [rho]) (n-i)))
    rw [hp]
    nlinarith
  have hs := Finset.sum_le_sum hterm
  have hr : (∑ i ∈ Finset.range (n+1), G (n-i)*rho^(n-i))=
      ∑ j ∈ Finset.range (n+1), G j*rho^j := by
    simpa using Finset.sum_range_reflect (fun j => G j*rho^j) (n+1)
  calc
    rho^n*(∑ i ∈ Finset.range (n+1), kernel i*G (n-i))=
        ∑ i ∈ Finset.range (n+1), kernel i*G (n-i)*rho^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ ≤ C*(∑ i ∈ Finset.range (n+1), G (n-i)*rho^(n-i)) := by
      simpa [Finset.mul_sum] using hs
    _ = C*(∑ j ∈ Finset.range (n+1), G j*rho^j) := by rw [hr]
    _ ≤ C*mass := mul_le_mul_of_nonneg_left hMass hC

theorem whole_eleven_tail_density_product (u v : ℕ) (T : ℕ → ℕ)
    (hu : 3 ≤ u) (hv : 4 ≤ v) (hT : ∀ i < 8, i+5 ≤ T i) :
    0 ≤ relative u*relative v ∧
    (25*30030:ℝ)*rho^16*(relative u*relative v) ≤ base^60 ∧
    60 ≤ (∑ i ∈ Finset.range 8, (T i-1)) := by
  have hpos (t : ℕ) (ht : 2 ≤ t) : 0 ≤ relative t := by
    dsimp [relative,FixedTerminalFourteenSlope.relative]
    exact div_nonneg (whole_capacity_eval_bounds t ht).1 (pow_nonneg (by norm_num [base]) _)
  have hru : relative u ≤ relative 4 := by
    simpa [relative] using FixedTerminalFourteenSlope.whole_relative_capacity_envelope 3 u (by omega) hu
  have hrv : relative v ≤ relative 4 := by
    simpa [relative] using FixedTerminalFourteenSlope.whole_relative_capacity_envelope 4 v (by omega) hv
  have hp : relative u*relative v ≤ relative 4*relative 4 :=
    mul_le_mul hru hrv (hpos v (by omega)) (hpos 4 (by omega))
  have hconst : (25*30030:ℝ)*rho^16*(relative 4*relative 4) ≤ base^60 := by
    norm_num [relative,FixedTerminalFourteenSlope.relative,stepEval,rho,base]
  have hb := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (25*30030:ℝ)*rho^16 by dsimp [rho]; positivity)
  have hsum : (∑ i ∈ Finset.range 8, (i+4)) ≤ ∑ i ∈ Finset.range 8, (T i-1) := by
    apply Finset.sum_le_sum
    intro i hi
    have h := hT i (Finset.mem_range.mp hi)
    omega
  have hn : (∑ i ∈ Finset.range 8, (i+4))=60 := by norm_num [Finset.sum_range_succ]
  rw [hn] at hsum
  exact ⟨mul_nonneg (hpos u (by omega)) (hpos v (by omega)),hb.trans hconst,hsum⟩

theorem whole_bulk_constant_density (m M0 : ℕ) (P d source long : ℝ)
    (hm : 34 ≤ m) (hM : M0+60 ≤ 2*m) (hP : 0 ≤ P)
    (hTemplate : (25*30030:ℝ)*rho^16*P ≤ base^60)
    (hRead : long*rho^m ≤ (30030:ℝ)*rho^16*base^M0*P)
    (hshort : source ≤ (m:ℝ)^5) (hd : d ≤ source+long) :
    20*d ≤ (2:ℝ)^m := by
  have hb0 : (0:ℝ) < base := by norm_num [base]
  have hr0 : (0:ℝ) < rho := by norm_num [rho]
  have hpow := pow_le_pow_right₀ (show (1:ℝ) ≤ base by norm_num [base]) hM
  have hbase : base^2 ≤ (2:ℝ)*rho := by norm_num [base,rho]
  have hbasepow := pow_le_pow_left₀ (show 0 ≤ base^2 by positivity) hbase m
  have htwo : base^(2*m) ≤ (2:ℝ)^m*rho^m := by
    simpa [pow_mul,mul_pow] using hbasepow
  have hscale := mul_le_mul_of_nonneg_left hRead (pow_nonneg (le_of_lt hb0) 60)
  have hdeg := mul_le_mul_of_nonneg_left (hpow.trans htwo)
    (show 0 ≤ (30030:ℝ)*rho^16*P by dsimp [rho]; positivity)
  have he : base^M0*base^60=base^(M0+60) := (pow_add _ _ _).symm
  have hscaled : rho^m*(base^60*long) ≤ rho^m*((30030:ℝ)*rho^16*P*(2:ℝ)^m) := by
    have hfull : (30030:ℝ)*rho^16*P*(base^M0*base^60) ≤
        (30030:ℝ)*rho^16*P*((2:ℝ)^m*rho^m) := by rw [he]; exact hdeg
    nlinarith
  have hclear := (mul_le_mul_iff_right₀ (pow_pos hr0 m)).mp hscaled
  have htemp := mul_le_mul_of_nonneg_right hTemplate (show 0 ≤ (2:ℝ)^m by positivity)
  have hlongprod : base^60*(25*long) ≤ base^60*(2:ℝ)^m := by nlinarith
  have hlong := (mul_le_mul_iff_right₀ (pow_pos hb0 60)).mp hlongprod
  have hpoly := whole_short_source_polynomial_budget m hm
  nlinarith

theorem whole_other_degree_density_powers (j m : ℕ) (hj : 56 ≤ j) (hm : 67 ≤ m) :
    100*shortRatio^j ≤ 1 ∧ 200*shortRatio^m ≤ 1 := by
  have h0 : (0:ℝ) ≤ shortRatio := by norm_num [shortRatio]
  have h1 : shortRatio ≤ 1 := by norm_num [shortRatio]
  have hpj := pow_le_pow_of_le_one h0 h1 hj
  have hpm := pow_le_pow_of_le_one h0 h1 hm
  have hbasej : (100:ℝ)*shortRatio^56 ≤ 1 := by norm_num [shortRatio]
  have hbasem : (200:ℝ)*shortRatio^67 ≤ 1 := by norm_num [shortRatio]
  constructor <;> nlinarith

theorem whole_low_first_missing_owner_rank_guard (K alpha h r e j : ℕ)
    (hK0 : 13 ≤ K) (hK1 : K ≤ 15) (ha : 1 ≤ alpha)
    (hbirth : alpha+e+3 ≤ K) (hcount : h ≤ 2*r+2+e)
    (hshared : j=alpha+h+r+2+e)
    (hout : (1+(K-2)*(K-1)/2)/2 < j-2) :
    e ≤ 2*r+2 := by
  interval_cases K <;> norm_num at hout <;> omega

theorem whole_fifth_raw_source_ratio (h r e : ℕ) (Q x y : ℝ)
    (hcount : h ≤ 2*r+2+e) (he : e ≤ 2*r+2)
    (hx : 0 ≤ x) (hprev : y ≤ x)
    (hHilbert : ((r:ℝ)+1)*Q ≤ ((h:ℝ)+(r:ℝ)+1)*x) :
    Q ≤ 5*(2*x-y) := by
  have hH : h+r+1 ≤ 5*(r+1) := by omega
  have hHR : (h:ℝ)+(r:ℝ)+1 ≤ 5*((r:ℝ)+1) := by exact_mod_cast hH
  have hmul := mul_le_mul_of_nonneg_right hHR hx
  have hq : ((r:ℝ)+1)*Q ≤ ((r:ℝ)+1)*(5*x) := by nlinarith
  have hQ := (mul_le_mul_iff_right₀ (show (0:ℝ) < (r:ℝ)+1 by positivity)).mp hq
  linarith

theorem whole_constant_density_source_payment (A B : ℕ → ℝ) (n : ℕ) (R : ℝ)
    (hA : ∀ k, A (k+1) ≤ 2*A k) (hAn : 0 ≤ A n)
    (hB0 : B 0=1) (hB1 : B 1=1)
    (hw : ∀ i ≤ n, 0 ≤ ActualDyadicSourcePayment.sourceWeight B i)
    (hD : 0 ≤ B (n+2)-B (n+1)) (hgap : A n ≤ 5*R)
    (hthin : 20*(B (n+2)-B (n+1)) ≤ (2:ℝ)^(n+2)) :
    A n-R-ActualDyadicSourcePayment.payment A B n ≤ 0 := by
  have hp := ActualDyadicSourcePayment.whole_nonnegative_weighted_source_budget A B n hA hB0 hB1 hw
  have hR : 0 ≤ R := by nlinarith
  have hg := mul_le_mul_of_nonneg_right hgap (show 0 ≤ 4*(B (n+2)-B (n+1)) by linarith)
  have ht := mul_le_mul_of_nonneg_left hthin hR
  have hcomp : 4*A n*(B (n+2)-B (n+1)) ≤ R*(2:ℝ)^(n+2) := by nlinarith
  have hprod : (2:ℝ)^(n+2)*(A n-R) ≤
      (2:ℝ)^(n+2)*ActualDyadicSourcePayment.payment A B n := by nlinarith
  have hfinal := (mul_le_mul_iff_right₀ (show (0:ℝ) < 2^(n+2) by positivity)).mp hprod
  linarith

theorem whole_eleven_template_degree_guards (K M m : ℕ) (hK : 13 ≤ K)
    (hM : 1+(K-2)*(K-1)/2 ≤ M) (hbulk : M ≤ 2*m) :
    34 ≤ m ∧ 56 ≤ 1+(K-3)*(K-2)/2 ∧ 66 ≤ (K-2)*(K-1)/2 ∧
    K-4 ≤ (1+(K-2)*(K-1)/2)/2 := by
  have hprodM : 11*12 ≤ (K-2)*(K-1) := Nat.mul_le_mul (by omega) (by omega)
  have hprodO : 10*11 ≤ (K-3)*(K-2) := Nat.mul_le_mul (by omega) (by omega)
  have hquad : 4*(K-2) ≤ (K-2)*(K-1) := by
    have h := Nat.mul_le_mul_left (K-2) (show 4 ≤ K-1 by omega)
    simpa [Nat.mul_comm] using h
  omega

#print axioms whole_short_source_polynomial_budget
#print axioms whole_seven_interval_weighted_coefficients
#print axioms whole_weighted_convolution_general_constant
#print axioms whole_eleven_tail_density_product
#print axioms whole_bulk_constant_density
#print axioms whole_other_degree_density_powers
#print axioms whole_low_first_missing_owner_rank_guard
#print axioms whole_fifth_raw_source_ratio
#print axioms whole_constant_density_source_payment
#print axioms whole_eleven_template_degree_guards
end
end FixedTerminalElevenDensity
