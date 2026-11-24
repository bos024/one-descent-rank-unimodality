import Mathlib

set_option maxHeartbeats 1000000
namespace HalfTailClosureArithmetic

theorem first_missing_mass_excludes_small_owner (K M : ℤ)
    (hK : 3 ≤ K) (hmass : K * (K - 1) ≤ 2 * M)
    (hsmall : M ≤ 3 * K - 7) : False := by
  have hp : 0 ≤ (K - 3) * (K - 4) := by
    by_cases heq : K = 3
    · subst K; norm_num
    · exact mul_nonneg (by omega) (by omega)
  nlinarith

theorem simultaneous_source_budgets_cannot_fail (K M s r : ℤ)
    (hK : 3 ≤ K) (hmass : K * (K - 1) ≤ 2 * M)
    (hshort : s ≤ 2 * K + 2 * r - 5)
    (hvirtual : M ≤ s + K - 2 * r - 2) : False := by
  apply first_missing_mass_excludes_small_owner K M hK hmass
  omega

theorem head_at_old_weight_has_only_three_cases (M s r : ℤ)
    (hMs : s ≤ M) (hr : 0 ≤ r) (hhead : M ≤ s - r + 1) :
    (M = s ∧ r = 0) ∨ (M = s ∧ r = 1) ∨ (M = s + 1 ∧ r = 0) := by
  omega

theorem balanced_initial_slab_main_degree (K M s m : ℤ)
    (hK : 3 ≤ K) (hmass : K * (K - 1) ≤ 2 * M)
    (hclose : M - 1 ≤ s) (hnormal : s + 1 ≤ 2 * m) :
    K - 1 ≤ m := by
  by_contra hfail
  have hp : 0 ≤ (K - 2) * (K - 3) := mul_nonneg (by omega) (by omega)
  have hm : m ≤ K - 2 := by omega
  nlinarith

theorem equal_weight_second_slab_main_degree (K M m : ℤ)
    (hK : 5 ≤ K) (hmass : K * (K - 1) ≤ 2 * M)
    (hnormal : M + 1 ≤ 2 * m) : K ≤ m := by
  by_contra hfail
  have hp : 0 < (K - 2) * (K - 3) := mul_pos (by omega) (by omega)
  have hm : m ≤ K - 1 := by omega
  nlinarith

theorem source_affected_half_edge (a b n : ℤ)
    (hweight : b ≤ a) (hhalf : 2 * n ≤ a + b)
    (hsource : a ≤ n + 1) :
    (n = a - 1 ∧ a - 2 ≤ b) ∨ (a = b ∧ n = a) := by
  omega

theorem source_free_head_before_old_weight (a c t M n k : ℤ)
    (happend : a = c + t) (hold : c ≤ M)
    (hsource : n + 1 < a) (hk : k = n + 1 - t) :
    k < c ∧ k < M := by
  omega

theorem half_window_maximal_leaving_head (M s r t n k : ℤ)
    (hn : n = M + r) (hk : k = n + 1 - t)
    (hhalf : 2 * n ≤ M + s + t) : k ≤ s - r + 1 := by
  omega

theorem locally_universal_terminal_crossing_impossible (K M s : ℤ)
    (hs : 3 ≤ s) (huniv : s + 2 < K)
    (hmass : K * (K - 1) ≤ 2 * M)
    (hmode : M ≤ 3 * s + 5) : False := by
  have hK : 6 ≤ K := by omega
  have hp : 0 ≤ (K - 6) * (K - 1) := mul_nonneg (by omega) (by omega)
  have hb : M ≤ 3 * K - 4 := by omega
  nlinarith

#print axioms first_missing_mass_excludes_small_owner
#print axioms simultaneous_source_budgets_cannot_fail
#print axioms head_at_old_weight_has_only_three_cases
#print axioms balanced_initial_slab_main_degree
#print axioms equal_weight_second_slab_main_degree
#print axioms source_affected_half_edge
#print axioms source_free_head_before_old_weight
#print axioms half_window_maximal_leaving_head
#print axioms locally_universal_terminal_crossing_impossible

end HalfTailClosureArithmetic
