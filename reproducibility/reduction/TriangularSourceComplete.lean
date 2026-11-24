import Mathlib

/-! Scoped kernels for triangular_source_curvature_complete.tex.
The actual-arm assembly and two complete finite jet enumerations are written
and independently reconstructed, not encoded end to end in this file. -/

namespace TriangularSourceComplete

theorem late_first_peak_pays_multiplicity
    (p current delta M : ℤ) (hcur : current=2*p-delta)
    (hrise : p≤current) (hfirst : p<M) : delta+1≤M := by omega

theorem triangular_budget_increment
    (d oldBudget newBudget : ℝ)
    (hold : 2*oldBudget=d*(d+1)-2)
    (hnew : 2*newBudget=(d+1)*(d+2)-2) :
    newBudget=oldBudget+d+1 := by nlinarith

theorem late_peak_two_source_terms_pay
    (oldBudget newBudget M curvature : ℝ)
    (hM : 1≤M) (hbudget : newBudget≤oldBudget)
    (hpay : oldBudget+M-1≤curvature) : newBudget≤curvature := by linarith

theorem tied_late_peak_two_source_terms_pay
    (oldBudget newBudget M d curvature : ℝ)
    (hM : d+1≤M) (hbudget : newBudget≤oldBudget+d+1)
    (hpay : oldBudget+M≤curvature) : newBudget≤curvature := by linarith

theorem peak_and_positive_tail_sum
    (S T : Finset ℤ) (f : ℤ → ℝ) (i : ℤ) (M : ℝ)
    (hi : i∈S) (hnot : i∉T) (hsub : T⊆S)
    (hnonneg : ∀ j∈S, 0≤f j) (hpeak : M≤f i)
    (htail : ∀ j∈T, 1≤f j) :
    M+(T.card : ℝ) ≤ ∑ j∈S, f j := by
  have hsumT : (T.card : ℝ) ≤ ∑ j∈T, f j := by
    calc
      (T.card : ℝ) = ∑ _j∈T, (1:ℝ) := by simp
      _ ≤ ∑ j∈T, f j := Finset.sum_le_sum htail
  have hsub2 : insert i T ⊆ S := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact hsub hj
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub2
    (fun j hj _ => hnonneg j hj)
  rw [Finset.sum_insert hnot] at hsum
  linarith

theorem early_peak_failure_rank_at_most_45
    (n ell M B curvature : ℤ)
    (hell : ell≤9) (hM : 1≤M) (hB : B≤35)
    (hpay : M+n-ell-3≤curvature) (hfail : curvature<B) : n≤45 := by omega

theorem early_peak_window_indices
    (n ell t R : ℤ) (hcross : ell<n-1)
    (hwindow : n≤ell+t) (hsupport : n≤R+1) :
    n-t≤ell+1 ∧ ell+1≤n-1 ∧ n-1≤R ∧ 0≤n-ell-2 := by omega

theorem doubling_bounds_mode_height
    (D : ℕ → ℝ) (hbase : D 2=1)
    (hdouble : ∀ n, 2≤n → D (n+1)≤2*D n) :
    ∀ n, 2≤n → D n≤(2:ℝ)^(n-2) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [hbase]
  | succ k hk ih =>
      have hd := hdouble k hk
      have he : k+1-2=(k-2)+1 := by omega
      rw [he, pow_succ]
      linarith

theorem early_mode_height_cap
    (D : ℕ → ℝ) (ell : ℕ) (hbase : D 2=1)
    (hdouble : ∀ n, 2≤n → D (n+1)≤2*D n)
    (hlo : 2≤ell) (hhi : ell≤9) : D ell≤128 := by
  have hbound := doubling_bounds_mode_height D hbase hdouble ell hlo
  have hp : (2:ℝ)^(ell-2)≤128 := by
    have he : ell-2≤7 := by omega
    calc
      (2:ℝ)^(ell-2) ≤ (2:ℝ)^7 := by
        gcongr
        norm_num
      _ = 128 := by norm_num
  exact hbound.trans hp

theorem strict_fall_excludes_a_later_first_mode
    (D : ℤ → ℝ) (i ell : ℤ)
    (hmono : MonotoneOn D (Set.Icc 2 ell))
    (hi : 3 ≤ i) (hfall : D i < D (i-1)) : ell < i := by
  by_contra! hn
  have hm := hmono (show i - 1 ∈ Set.Icc 2 ell by constructor <;> omega)
    (show i ∈ Set.Icc 2 ell by constructor <;> omega) (show i - 1 ≤ i by omega)
  linarith

theorem low_first_weight_exceptional_ranks
    (kap n : ℤ) (hk : kap≤7)
    (hn : n=kap+3 ∨ n=kap+4 ∨ n=kap+5) : n≤12 := by omega

theorem quadratic_pair_budget
    (a b A B : ℝ) (ha : a*a≤2*A) (hb : b*b≤2*B) :
    a*b≤A+B := by nlinarith [sq_nonneg (a-b)]

#print axioms late_first_peak_pays_multiplicity
#print axioms triangular_budget_increment
#print axioms late_peak_two_source_terms_pay
#print axioms tied_late_peak_two_source_terms_pay
#print axioms peak_and_positive_tail_sum
#print axioms early_peak_failure_rank_at_most_45
#print axioms early_peak_window_indices
#print axioms doubling_bounds_mode_height
#print axioms early_mode_height_cap
#print axioms strict_fall_excludes_a_later_first_mode
#print axioms low_first_weight_exceptional_ranks
#print axioms quadratic_pair_budget

end TriangularSourceComplete
