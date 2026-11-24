import Mathlib

namespace CountPrefixSeparator

theorem unbounded_cascade_prefix_nonnegative
    (A B : ℕ → ℕ → ℤ) (t : ℕ → ℕ)
    (hbase : ∀ n, n ≤ 1 → 0 ≤ A 0 n)
    (hB : ∀ h n, 0 ≤ B h n)
    (hrec : ∀ h n, A (h+1) n = B h n+
      ∑ j ∈ Finset.range (min (t h) n), A h (n-j-1)) :
    ∀ h n, n ≤ h+1 → 0 ≤ A h n := by
  intro h
  induction h with
  | zero => exact hbase
  | succ h ih =>
      intro n hn
      rw [hrec]
      apply add_nonneg (hB h n)
      apply Finset.sum_nonneg
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right _ _)
      exact ih (n-j-1) (by omega)

theorem Fibonacci_and_doubling_pay_three_halves (a b c : ℤ)
    (hF : a+b ≤ c) (hdouble : b ≤ 2*a) : 3*b ≤ 2*c := by omega

theorem one_negative_coefficient_compensation (s : Finset ℕ) (W : ℕ → ℤ) (j : ℕ)
    (h1 : W 1= -1) (hW : ∀ i ∈ s, i≠1 → 0 ≤ W i)
    (hj : j≠1) (hpay : 1 ≤ W j) (hmem : 1 ∈ s → j ∈ s) :
    0 ≤ ∑ i ∈ s, W i := by
  by_cases hin : 1 ∈ s
  · have hjmem : j ∈ s.erase 1 := Finset.mem_erase.mpr ⟨hj,hmem hin⟩
    have hpos : ∀ i ∈ s.erase 1, 0 ≤ W i := by
      intro i hi
      exact hW i (Finset.mem_of_mem_erase hi) (Finset.mem_erase.mp hi).1
    have hs := Finset.single_le_sum hpos hjmem
    have he := Finset.sum_erase_add s W hin
    omega
  · exact Finset.sum_nonneg fun i hi => hW i hi (by intro he; subst i; exact hin hi)

theorem interval_contains_compensator (lo u : ℕ)
    (hwidth : 2 ≤ u+1-lo) (hlo : lo ≤ 1) (hu : 1 ≤ u) :
    (lo=0 ∧ u=1) ∨ (lo ≤ 2 ∧ 2 ≤ u) := by omega

theorem stationary_budget_jet_allocation (s sigmaX sigmaY : ℕ)
    (hbudget : s ≤ sigmaX+sigmaY) :
    ∃ mX mY : ℕ, mX+mY=s ∧ mX ≤ s ∧ mY ≤ s ∧
      s-sigmaY ≤ mX ∧ s-sigmaX ≤ mY := by
  refine ⟨s-sigmaY,s-(s-sigmaY),?_,?_,?_,?_,?_⟩ <;> omega

theorem allocated_unknown_reads_stay_inside_count_prefix
    (p q h g s mX mY : ℕ)
    (hp : p ≤ h+2) (hq : q ≤ g+2)
    (hx : s-(g+2-q) ≤ mX) (hy : s-(h+2-p) ≤ mY) :
    q+s-mX-1 ≤ g+1 ∧ p+s-mY-1 ≤ h+1 := by omega

#print axioms unbounded_cascade_prefix_nonnegative
#print axioms Fibonacci_and_doubling_pay_three_halves
#print axioms one_negative_coefficient_compensation
#print axioms interval_contains_compensator
#print axioms stationary_budget_jet_allocation
#print axioms allocated_unknown_reads_stay_inside_count_prefix

end CountPrefixSeparator
