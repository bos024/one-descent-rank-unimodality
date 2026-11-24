import Mathlib

/-! Generic kernels for the conditional large-first-weight TC append proof.
Actual source identities, profile bounds and peak-crossing theorem are the
written assembly. No complete TC or original-conjecture proof is asserted. -/

namespace TriangularSourceLargeAppend

theorem small_multiplicity_profile_budget (d : ℤ) (hd : 1≤d) (hsmall : d≤5) :
    d*(d+3) ≤ 8*d := by nlinarith

theorem large_profile_induction (f : ℕ → ℤ)
    (hbase : 27 ≤ f 6)
    (hstep : ∀ n : ℕ, 6≤n → f n + (n:ℤ)+2 ≤ f (n+1)) :
    ∀ n : ℕ, 6≤n → (n:ℤ)*((n:ℤ)+3) ≤ 2*f n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num at *; linarith
  | succ k hk ih =>
      have hs := hstep k hk
      push_cast
      nlinarith

theorem two_triangular_budgets (d : ℤ) (hd : 3≤d) :
    d*(d+3) ≤ 2*(d*(d+1)-2) := by
  have h := mul_nonneg (show 0≤d-3 by omega) (show 0≤d+2 by omega)
  nlinarith

theorem exceptional_multiplicity_budgets : 2*1≥2 ∧ 3*2≥5 := by decide

theorem finite_two_terms_budget (S : Finset ℤ) (f : ℤ → ℝ) (i j : ℤ)
    (hi : i∈S) (hj : j∈S) (hne : i≠j)
    (hnonneg : ∀ k∈S, 0≤f k) : f i+f j ≤ ∑ k∈S, f k := by
  have hsub : ({i,j} : Finset ℤ) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k hk _ => hnonneg k hk)
  simpa [Finset.sum_pair hne] using hs

theorem finite_three_terms_budget (S : Finset ℤ) (f : ℤ → ℝ) (i j k : ℤ)
    (hi : i∈S) (hj : j∈S) (hk : k∈S)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hnonneg : ∀ r∈S, 0≤f r) : f i+f j+f k ≤ ∑ r∈S, f r := by
  have hsub : ({i,j,k} : Finset ℤ) ⊆ S := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun r hr _ => hnonneg r hr)
  simpa [Finset.sum_insert, hij, hik, hjk, Finset.sum_pair, add_assoc] using hs

theorem preserving_dent_distinct_birth (kap t n : ℤ)
    (hk : 8≤kap) (_ht : kap<t) (hn : kap+4≤n) (hdent : n=t+2) :
    n-t≤kap ∧ kap≤n-1 ∧ kap≠n-1 ∧ 1≤kap := by omega

theorem tied_two_and_three_indices (kap n ell : ℤ)
    (hk : 8≤kap) (hn : kap+5≤n) (hell : n-1≤ell) :
    (kap+3≤n-2 ∧ n-2≤ell ∧ n-kap≤n-2) ∧
    (kap+6≤n → kap+3≤n-3 ∧ n-3≤ell ∧ n-kap≤n-3) := by omega

#print axioms small_multiplicity_profile_budget
#print axioms large_profile_induction
#print axioms two_triangular_budgets
#print axioms exceptional_multiplicity_budgets
#print axioms finite_two_terms_budget
#print axioms finite_three_terms_budget
#print axioms preserving_dent_distinct_birth
#print axioms tied_two_and_three_indices

end TriangularSourceLargeAppend
