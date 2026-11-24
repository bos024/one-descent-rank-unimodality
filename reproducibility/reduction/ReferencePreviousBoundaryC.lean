import Mathlib
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace ReferencePreviousBoundaryC

theorem golden_tight_lower (q : ℝ) (hq : 0 < q) (heq : q^2+q=1) :
    (55:ℝ)/89 < q := by
  by_contra hn
  have hl : q ≤ (55:ℝ)/89 := le_of_not_gt hn
  have hs := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ (55:ℝ)/89+q by positivity)
  nlinarith

theorem two_factor_lower_margin (q : ℝ) (hq : 0 < q) (heq : q^2+q=1) :
    q < (1-q^4)^2 := by
  have hid : (1-q^4)^2-q=2*q^6 := by
    linear_combination (q^6-q^5-q^3-q^2-1)*heq
  nlinarith [pow_pos hq 6]

theorem three_factor_odd_margin (q : ℝ) (hq : 0 < q) (heq : q^2+q=1) :
    1 < (1+q^3)*(1-q^4) := by
  have hid : (1+q^3)*(1-q^4)-1=q^6 := by
    linear_combination (-q^3-q^5)*heq
  nlinarith [pow_pos hq 6]

theorem three_factor_even_margins (q : ℝ) (hq : 0 < q) (heq : q^2+q=1) :
    1 < (1+q^3)*(1-q^6)^2 ∧ 1 < (1+q^3)*(1-q^4)*(1-q^8) := by
  have hl := golden_tight_lower q hq heq
  have h66 : (1+q^3)*(1-q^6)^2-1 = -257+416*q := by
    linear_combination
      (-257+159*q-98*q^2+60*q^3-38*q^4+22*q^5-14*q^6+8*q^7-6*q^8+4*q^9-2*q^10+2*q^11-q^12+q^13)*heq
  have h48 : (1+q^3)*(1-q^4)*(1-q^8)-1 = -241+390*q := by
    linear_combination
      (-241+149*q-92*q^2+56*q^3-35*q^4+21*q^5-14*q^6+8*q^7-5*q^8+3*q^9-2*q^10+2*q^11-q^12+q^13)*heq
  constructor <;> nlinarith

theorem even_capacity_exceptions (a b : ℕ) (ha : 4≤a) (hab : a≤b)
    (haeven : a%2=0) (hbeven : b%2=0)
    (hex4 : ¬(a=4 ∧ b=4)) (hex6 : ¬(a=4 ∧ b=6)) :
    6≤a ∨ (a=4 ∧ 8≤b) := by omega

def F (n : ℕ) : ℤ := Nat.fib n

theorem fib_norm (n : ℕ) : F n^2+F n*F (n+1)-F (n+1)^2=(-1:ℤ)^(n+1) := by
  induction n with
  | zero => norm_num [F]
  | succ n ih =>
      have hr : F (n+2)=F n+F (n+1) := by simp [F,Nat.fib_add_two]
      have hp : (-1:ℤ)^(n+1+1)=-((-1:ℤ)^(n+1)) := by rw [pow_succ]; ring
      rw [show n+1+1=n+2 by omega,hr]
      rw [show n+2=(n+1)+1 by omega,pow_succ]
      nlinarith [ih]

theorem binary_envelope_identity (n : ℕ) :
    (F (n+5)-1)*(2*F (n+3)-1)-(F (n+4)-1)*(2*F (n+4)-1)=
      F n+2*(-1:ℤ)^(n+4) := by
  have h2 : F (n+2)=F n+F (n+1) := by simp [F,Nat.fib_add_two]
  have h3 : F (n+3)=F (n+1)+F (n+2) := by
    simpa only [show n+3=(n+1)+2 by omega,show n+2=n+1+1 by omega] using (show F ((n+1)+2)=F (n+1)+F ((n+1)+1) by simp [F,Nat.fib_add_two])
  have h4 : F (n+4)=F (n+2)+F (n+3) := by
    simpa only [show n+4=(n+2)+2 by omega,show n+3=n+2+1 by omega] using (show F ((n+2)+2)=F (n+2)+F ((n+2)+1) by simp [F,Nat.fib_add_two])
  have h5 : F (n+5)=F (n+3)+F (n+4) := by
    simpa only [show n+5=(n+3)+2 by omega,show n+4=n+3+1 by omega] using (show F ((n+3)+2)=F (n+3)+F ((n+3)+1) by simp [F,Nat.fib_add_two])
  have hn := fib_norm (n+3)
  rw [show n+3+1=n+4 by omega] at hn
  have hlin : 2*F (n+4)-3*F (n+3)=F n := by linarith
  calc
    _ = 2*(F (n+3)^2+F (n+3)*F (n+4)-F (n+4)^2)+2*F (n+4)-3*F (n+3) := by
      rw [h5]
      ring
    _ = F n+2*(-1:ℤ)^(n+4) := by rw [hn]; linarith

theorem large_fib_envelope (n : ℕ) (hn : 4≤n) :
    1≤F n+2*(-1:ℤ)^(n+4) := by
  have hfN : Nat.fib 4≤Nat.fib n := Nat.fib_mono hn
  have hfour : Nat.fib 4=3 := by decide
  rw [hfour] at hfN
  have hf : (3:ℤ) ≤ F n := by
    unfold F
    exact_mod_cast hfN
  have hb : ∀ k : ℕ, (-1:ℤ)≤(-1:ℤ)^k ∧ (-1:ℤ)^k≤1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; constructor <;> nlinarith
  nlinarith [(hb (n+4)).1]

def referenceAt : List ℕ → ℕ → ℤ
  | [],n => Nat.fib (n+1)
  | t::V,n => (if n=0 then 1 else 0)+∑ i ∈ Finset.range (min t n), referenceAt V (n-1-i)

def cum (V : List ℕ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n+1), referenceAt V i
def deriv (V : List ℕ) (n : ℕ) : ℤ := referenceAt V n-referenceAt V (n-1)
def boundaryC (V : List ℕ) (N : ℕ) : Bool :=
  (List.range (N-3)).all (fun k => decide (cum V (k+1)*deriv V (N-1)≥cum V k*deriv V N))

theorem exact_three_four_four : boundaryC [4,4,3] 10 = true := by decide +kernel
theorem exact_three_four_six : boundaryC [6,4,3] 12 = true := by decide +kernel
theorem exact_three_six_four : boundaryC [4,6,3] 12 = true := by decide +kernel
theorem exact_three_four : boundaryC [4,3] 6 = true := by decide +kernel

#print axioms golden_tight_lower
#print axioms two_factor_lower_margin
#print axioms three_factor_odd_margin
#print axioms three_factor_even_margins
#print axioms even_capacity_exceptions
#print axioms fib_norm
#print axioms binary_envelope_identity
#print axioms large_fib_envelope
#print axioms exact_three_four_four
#print axioms exact_three_four_six
#print axioms exact_three_six_four
#print axioms exact_three_four

end ReferencePreviousBoundaryC
