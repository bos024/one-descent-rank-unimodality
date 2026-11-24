import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace TribonacciInverseTerminalNorm

def Q (a x y : ℝ) : ℝ := x^2+a*x*y+(a^2+a-1)*y^2

theorem exact_binary_terminal_norm (a x y : ℝ) :
    Q a ((1-a)*x-(a^2+a-1)*y) (x+y)=a^2*Q a x y := by
  dsimp [Q]
  ring

theorem exact_ternary_terminal_norm (a x y : ℝ) (hq : a^3+2*a^2=2) :
    Q a (2*(1-a)*x-(a^2+a-1)*(1-a)*y)
      ((1-a)*x+(2-a^2-a)*y)=(1-a)*Q a x y := by
  dsimp [Q]
  linear_combination -(1-a)*(x^2+a*x*y+(a^2+a-1)*y^2)*hq

theorem whole_unbounded_two_count_norm (T : ℕ → ℕ → ℝ) (a : ℝ)
    (h0 : T 0 0=1)
    (hB : ∀ u,T (u+1) 0=a^2*T u 0)
    (hT : ∀ u r,T u (r+1)=(1-a)*T u r) :
    ∀ u r,T u r=(a^2)^u*(1-a)^r := by
  have hb : ∀ u,T u 0=(a^2)^u := by
    intro u
    induction u with
    | zero => simpa using h0
    | succ u ih => rw [hB,ih,pow_succ]; ring
  intro u r
  induction r with
  | zero => simpa using hb u
  | succ r ih => rw [hT,ih,pow_succ]; ring

theorem terminal_form_coercive (a x y : ℝ)
    (hlo : 83/100 ≤ a) (hhi : a ≤ 84/100) :
    (x^2+y^2)/10 ≤ Q a x y := by
  have ha : 0 ≤ a := by linarith
  have ha2 := mul_self_le_mul_self (show (0:ℝ) ≤ 83/100 by norm_num) hlo
  have h1 : 0 ≤ 1-a/2-1/10 := by linarith
  have h2 : 0 ≤ a^2+a/2-1-1/10 := by nlinarith
  have hc := mul_nonneg (show 0 ≤ a/2 by linarith) (sq_nonneg (x+y))
  have hx := mul_nonneg h1 (sq_nonneg x)
  have hy := mul_nonneg h2 (sq_nonneg y)
  dsimp [Q]
  nlinarith

theorem geometric_eighteen_terminal_bound :
    ∀ w : ℕ,18 ≤ w → ((3:ℝ)/4)^w ≤ 1/160 := by
  have hp : ∀ k : ℕ,((3:ℝ)/4)^k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith [pow_nonneg (show (0:ℝ) ≤ 3/4 by norm_num) k]
  intro w hw
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hw
  rw [hk,pow_add]
  have h := hp k
  norm_num
  nlinarith

theorem complete_terminal_quarter_box (a x y : ℝ)
    (hlo : 83/100 ≤ a) (hhi : a ≤ 84/100)
    (hN : Q a x y ≤ 1/160) :
    -(1/4) ≤ x ∧ x ≤ 1/4 ∧ -(1/4) ≤ y ∧ y ≤ 1/4 := by
  have hC := terminal_form_coercive a x y hlo hhi
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  constructor
  · nlinarith [sq_nonneg (x+1/4)]
  constructor
  · nlinarith [sq_nonneg (x-1/4)]
  constructor
  · nlinarith [sq_nonneg (y+1/4)]
  · nlinarith [sq_nonneg (y-1/4)]

#print axioms exact_binary_terminal_norm
#print axioms exact_ternary_terminal_norm
#print axioms whole_unbounded_two_count_norm
#print axioms terminal_form_coercive
#print axioms geometric_eighteen_terminal_bound
#print axioms complete_terminal_quarter_box

end TribonacciInverseTerminalNorm
