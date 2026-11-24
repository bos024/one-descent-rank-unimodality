import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace TribonacciRichReverseQuotient

def R (a b x y : ℝ) : ℝ := b*x^2+a*x*y+y^2

theorem complete_reverse_binary_norm (a b l x y : ℝ) (h : l*b=1) :
    R a b ((1-l*a)*x-l*y) (x+y)=(1-l*a+l)*R a b x y ∧
    R a b (x+l*y) (-x+(1-l*a)*y)=(1-l*a+l)*R a b x y := by
  constructor
  · dsimp [R]
    linear_combination ((l*a^2-a-1)*x^2+2*(l*a-1)*x*y+l*y^2)*h
  · dsimp [R]
    linear_combination ((a-1)*x^2+2*x*y+l*y^2)*h

theorem complete_reverse_ternary_norm (a b x y : ℝ) :
    R a b y (-b*x-a*y)=b*R a b x y ∧
    R a b (-a*x-y) (b*x)=b*R a b x y := by
  constructor <;> dsimp [R] <;> ring

theorem whole_reverse_two_count_norm (T : ℕ → ℕ → ℝ) (b S : ℝ)
    (h0 : T 0 0=b) (hB : ∀ u,T (u+1) 0=S*T u 0)
    (hT : ∀ u r,T u (r+1)=b*T u r) :
    ∀ u r,T u r=b*S^u*b^r := by
  have hb : ∀ u,T u 0=b*S^u := by
    intro u
    induction u with
    | zero => simpa using h0
    | succ u ih => rw [hB,ih,pow_succ];ring
  intro u r
  induction r with
  | zero => simpa using hb u
  | succ r ih => rw [hT,ih,pow_succ];ring

theorem strong_reverse_quarter_box (a b x y : ℝ)
    (hb : 1/2 ≤ b) (ha : a^2 ≤ 3/4) (hN : R a b x y ≤ 1/64) :
    -(1/4) ≤ x ∧ x ≤ 1/4 ∧ -(1/4) ≤ y ∧ y ≤ 1/4 := by
  have hx := mul_nonneg (show 0 ≤ b-1/2 by linarith) (sq_nonneg x)
  have hy := mul_nonneg (show 0 ≤ 3/4-a^2 by linarith) (sq_nonneg y)
  have hs := sq_nonneg (x/2+a*y)
  have hc : (x^2+y^2)/4 ≤ R a b x y := by dsimp [R];nlinarith
  constructor
  · nlinarith [sq_nonneg y,sq_nonneg (x+1/4)]
  constructor
  · nlinarith [sq_nonneg y,sq_nonneg (x-1/4)]
  constructor
  · nlinarith [sq_nonneg x,sq_nonneg (y+1/4)]
  · nlinarith [sq_nonneg x,sq_nonneg (y-1/4)]

theorem unit_powers (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∀ k : ℕ,t^k ≤ 1 := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hp := pow_nonneg h0 k
      have h := mul_le_mul_of_nonneg_left h1 hp
      nlinarith

theorem rich_norm_uniform_payment (b P : ℝ) (u k : ℕ)
    (hb0 : 0 ≤ b) (hb : b ≤ 3/5) (hP0 : 0 ≤ P) (hP : P ≤ 2/5)
    (hu : 4 ≤ u) : b*P^u*b^k ≤ 1/64 := by
  have hb1 : b ≤ 1 := by linarith
  have hP1 : P ≤ 1 := by linarith
  have hp2 : P^2 ≤ (2/5:ℝ)^2 := by nlinarith [mul_self_le_mul_self hP0 hP]
  have hp4 : P^4 ≤ (2/5:ℝ)^4 := by
    have h := mul_self_le_mul_self (sq_nonneg P) hp2
    nlinarith
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hu
  have hj1 := unit_powers P hP0 hP1 j
  have hk1 := unit_powers b hb0 hb1 k
  have hprod : P^j*b^k ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hk1 (pow_nonneg hP0 j)
    simp only [mul_one] at h
    exact h.trans hj1
  have hbase := mul_le_mul hb hp4 (by positivity) (by norm_num : (0:ℝ) ≤ 3/5)
  rw [hj,pow_add]
  calc
    b*(P^4*P^j)*b^k = (b*P^4)*(P^j*b^k) := by ring
    _ ≤ b*P^4 := by nlinarith [mul_le_mul_of_nonneg_left hprod (show 0 ≤ b*P^4 by positivity)]
    _ ≤ (3/5:ℝ)*(2/5:ℝ)^4 := hbase
    _ ≤ 1/64 := by norm_num

theorem binary_increasing_norm_cone_induction (P : ℕ → Prop) (N : ℕ → ℝ)
    (c : ℝ) (h0 : P 0) (hN : ∀ u,N u ≤ N (u+1))
    (hstep : ∀ u,N u ≤ c → P u → P (u+1)) :
    ∀ u,N u ≤ c → P u := by
  intro u
  induction u with
  | zero => intro _;exact h0
  | succ u ih =>
      intro hs
      have hold := (hN u).trans hs
      exact hstep u hold (ih hold)

#print axioms complete_reverse_binary_norm
#print axioms complete_reverse_ternary_norm
#print axioms whole_reverse_two_count_norm
#print axioms strong_reverse_quarter_box
#print axioms rich_norm_uniform_payment
#print axioms binary_increasing_norm_cone_induction

end TribonacciRichReverseQuotient
