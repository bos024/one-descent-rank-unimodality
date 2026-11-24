import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace TernaryForwardInverse

theorem golden_interval (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    618033988/1000000000 ≤ q ∧ q ≤ 618033989/1000000000 := by
  constructor
  · by_contra! h
    have hsq := mul_self_le_mul_self hp (le_of_lt h)
    nlinarith
  · by_contra! h
    have hsq := mul_self_le_mul_self (show (0:ℝ) ≤ 618033989/1000000000 by norm_num)
      (le_of_lt h)
    nlinarith

theorem potential_binary_contraction (q w τ : ℝ)
    (hq : q^2+q=1) (hp : 0 ≤ q) (hb : q ≤ 1) (hw : 1 ≤ w) (ht : 0 ≤ τ) :
    2*(1+q+q*(w+1))*(q^2*τ) ≤ 2*(1+q+q*w)*τ := by
  have hid : (1+q+q*w)-q^2*(1+q+q*(w+1)) = q*(1+q+q*w)-q^3 := by
    linear_combination -(1+q+q*w)*(hq)
  have hq3 : q^3 ≤ q := by
    have h := mul_nonneg hp (show 0 ≤ 1-q^2 by nlinarith)
    nlinarith
  have hqw := mul_nonneg hp (show 0 ≤ q*w by positivity)
  have hd : 0 ≤ (1+q+q*w)-q^2*(1+q+q*(w+1)) := by nlinarith
  have h := mul_nonneg hd ht
  nlinarith

theorem potential_ternary_contraction (q w τ : ℝ)
    (hq : q^2+q=1) (hp : 0 ≤ q) (hw : 1 ≤ w) (ht : 0 ≤ τ) :
    2*(1+q+q*(w+1))*(2*q^2*τ) ≤ 2*(1+q+q*w)*τ := by
  have hqi := golden_interval q hq hp
  have hid : (1+q+q*w)-2*q^2*(1+q+q*(w+1))
      = (2*q-1)*(q+q*w-1) := by
    linear_combination -2*(2*q+q*w)*hq
  have hqw : q ≤ q*w := by nlinarith
  have hd : 0 ≤ (1+q+q*w)-2*q^2*(1+q+q*(w+1)) := by
    rw [hid]
    apply mul_nonneg <;> linarith [hqi.1]
  have h := mul_nonneg hd ht
  nlinarith

theorem mixed_unbounded_terminal_potential (q : ℝ)
    (hq : q^2+q=1) (hp : 0 ≤ q) :
    ∀ m r : ℕ,
      2*(1+q+q*((m+1+r:ℕ):ℝ))*((q^2)^(m+1)*(2*q^2)^r) ≤ (1+q)^2 := by
  have hqi := golden_interval q hq hp
  have hq1 : q ≤ 1 := by linarith [hqi.2]
  have hb : 2*(1+q+q*(1:ℝ))*q^2 ≤ (1+q)^2 := by
    have hid : (1+q)^2-2*(1+q+q*(1:ℝ))*q^2=4-5*q := by
      linear_combination (3-4*q)*hq
    linarith [hqi.2]
  have hm : ∀ m : ℕ,2*(1+q+q*((m+1:ℕ):ℝ))*(q^2)^(m+1) ≤ (1+q)^2 := by
    intro m
    induction m with
    | zero => simpa using hb
    | succ m ih =>
        have h := potential_binary_contraction q ((m+1:ℕ):ℝ) ((q^2)^(m+1))
          hq hp hq1 (by exact_mod_cast (show 1 ≤ m+1 by omega)) (by positivity)
        have hh := h.trans ih
        convert hh using 1 <;> simp only [pow_succ,Nat.cast_add,Nat.cast_one] <;> ring
  intro m r
  induction r with
  | zero => simpa using hm m
  | succ r ih =>
      have h := potential_ternary_contraction q ((m+1+r:ℕ):ℝ)
        ((q^2)^(m+1)*(2*q^2)^r) hq hp
        (by exact_mod_cast (show 1 ≤ m+1+r by omega)) (by positivity)
      have hh := h.trans ih
      convert hh using 1 <;> simp only [pow_succ,Nat.cast_add,Nat.cast_one] <;> ring

theorem ternary_terminal_minor_identity (q w τ : ℝ) (hq : q^2+q=1) :
    ((1+q)*(1-τ)+q^2*τ)^2
      -((1+q)*w-1+2*τ)*(2*q^2*τ)
       =(1+q)^2-2*(1+q+q*w)*τ := by
  linear_combination (2*q*(1-w)*τ+(q^2-3*q-1)*τ^2)*hq

theorem ternary_terminal_minor_paid (q w τ : ℝ) (hq : q^2+q=1)
    (hbudget : 2*(1+q+q*w)*τ ≤ (1+q)^2) :
    ((1+q)*w-1+2*τ)*(2*q^2*τ) ≤ ((1+q)*(1-τ)+q^2*τ)^2 := by
  have hi := ternary_terminal_minor_identity q w τ hq
  linarith

theorem positive_ternary_corrected_edges (q v τ : ℝ)
    (hq : q^2+q=1) (hp : 0 < q) (hv : 0 < v) (ht : 0 < τ) :
    0 < v+q^2*τ ∧ 0 < 2*q^2*τ ∧ v+q^2*τ ≤ v+τ := by
  constructor
  · positivity
  constructor
  · positivity
  have h := mul_nonneg (le_of_lt hp) (le_of_lt ht)
  nlinarith

theorem lowering_next_preserves_minor (a b c d : ℝ)
    (ha : 0 ≤ a) (hminor : a*c ≤ b^2) (hd : d ≤ c) : a*d ≤ b^2 := by
  exact (mul_le_mul_of_nonneg_left hd ha).trans hminor

#print axioms golden_interval
#print axioms potential_binary_contraction
#print axioms potential_ternary_contraction
#print axioms mixed_unbounded_terminal_potential
#print axioms ternary_terminal_minor_identity
#print axioms ternary_terminal_minor_paid
#print axioms positive_ternary_corrected_edges
#print axioms lowering_next_preserves_minor

end TernaryForwardInverse
