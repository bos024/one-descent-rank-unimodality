import Mathlib
set_option maxHeartbeats 2000000
namespace CoupledSourceWindowA2

theorem closed_source_payment_propagates_weighted_fall
    (previous current next incoming outgoing T H : ℝ)
    (hcurrent : 2*current-previous=incoming-outgoing)
    (hnext : 2*next-current=(incoming+T)-(outgoing+H))
    (hfall : 2*current ≤ previous) (hpayment : T ≤ H) :
    2*next ≤ current := by linarith

theorem negative_source_tail_propagates_window_fall
    (current next incoming_next outgoing_next : ℝ)
    (hnext : 2*next-current=incoming_next-outgoing_next)
    (hnegative : incoming_next ≤ 0) (hhead : 0 ≤ outgoing_next) :
    2*next ≤ current := by linarith

theorem complete_halving_tail_finite_sum (v : ℕ → ℝ)
    (hhalf : ∀ n, 2*v (n+1) ≤ v n) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), v i) ≤ 2*v 0-v N := by
  induction N with
  | zero => simp; linarith
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hh := hhalf N
    linarith

theorem entire_finite_halving_tail_budget (v : ℕ → ℝ)
    (hhalf : ∀ n, 2*v (n+1) ≤ v n) (hpos : ∀ n, 0 ≤ v n) (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), v i) ≤ 2*v 0 := by
  have hh := complete_halving_tail_finite_sum v hhalf N
  have hp := hpos N
  linarith

theorem late_outgoing_head_geometric_payment (current next u v : ℝ)
    (hrec : next=current-u-v) (hbudget : current ≤ 2*u) (hv : 0 ≤ v) :
    2*next ≤ current := by linarith

theorem relative_raw_kernel_surplus_pays_closed_source_gap
    (lambda d incoming outgoing C T H : ℝ)
    (hl : 0 ≤ lambda) (hd : d ≤ incoming) (hgap : incoming ≤ outgoing)
    (hC : C=lambda*d) (hT : T ≤ C) (hH : lambda*outgoing+1 ≤ H) :
    T<H := by
  have hh := mul_nonneg hl (show 0 ≤ outgoing-d by linarith)
  nlinarith only [hh,hC,hT,hH]

theorem complete_UI_head_boundary_and_closed_cross_no_revival
    (f g : ℕ → ℝ) (c : ℕ)
    (hhead : ∀ n, n ≤ c → f n=g n)
    (hboundary : f (c+1) ≤ g (c+1))
    (hG : ∀ i j, i<j → g (i+1)<g i → g (j+1) ≤ g j)
    (hcross : ∀ n, c ≤ n → f (n+1) ≤ f n → f (n+2) ≤ f (n+1)) :
    ∀ i j, i<j → f (i+1)<f i → f (j+1) ≤ f j := by
  have hdesc : ∀ s, c ≤ s → f (s+1) ≤ f s →
      ∀ j, s ≤ j → f (j+1) ≤ f j := by
    intro s hs hf j hj
    induction j,hj using Nat.le_induction with
    | base => exact hf
    | succ j hj ih => exact hcross j (by omega) ih
  intro i j hij hfall
  by_cases hj : j<c
  · have hiG : g (i+1)<g i := by
      rw [←hhead (i+1) (by omega),←hhead i (by omega)]
      exact hfall
    rw [hhead (j+1) (by omega),hhead j (by omega)]
    exact hG i j hij hiG
  · by_cases hi : i<c
    · have hiG : g (i+1)<g i := by
        rw [←hhead (i+1) (by omega),←hhead i (by omega)]
        exact hfall
      have hbG := hG i c hi hiG
      have hb : f (c+1) ≤ f c := by rw [hhead c le_rfl]; linarith
      exact hdesc c le_rfl hb j (by omega)
    · exact hdesc i (by omega) (le_of_lt hfall) j (by omega)

theorem complete_two_head_prefix_selection (m t : ℕ) (ht : 1 ≤ t) :
    let c := max m (t-1)
    m<c+1 ∧ t ≤ c+1 ∧
    ((c=m ∧ t-1 ≤ m) ∨ (c=t-1 ∧ m<t-1)) := by
  dsimp
  omega

theorem first_missing_nine_complete_exception_head_read_guards
    (a b j n k : ℕ) (hj : j+n=a+b)
    (hsecond : k+n+2<a+b) (howner : j ≤ a+1) (hjmax : j ≤ 10) :
    k+1 ≤ 8 ∧ k+1 ≤ a-1 := by omega

#print axioms closed_source_payment_propagates_weighted_fall
#print axioms negative_source_tail_propagates_window_fall
#print axioms complete_halving_tail_finite_sum
#print axioms entire_finite_halving_tail_budget
#print axioms late_outgoing_head_geometric_payment
#print axioms relative_raw_kernel_surplus_pays_closed_source_gap
#print axioms complete_UI_head_boundary_and_closed_cross_no_revival
#print axioms complete_two_head_prefix_selection
#print axioms first_missing_nine_complete_exception_head_read_guards
end CoupledSourceWindowA2
