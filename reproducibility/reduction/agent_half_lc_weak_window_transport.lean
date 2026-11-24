import Mathlib

namespace AgentHalfLCWeakWindowTransport

theorem crossing_window_curvature_nonpositive
    (deltaNow deltaNext enter leave : ℝ)
    (he : enter ≤ 0) (hl : 0 ≤ leave) (htail : deltaNext ≤ 0)
    (hidentity : deltaNext-deltaNow=enter-leave) :
    2*deltaNext-deltaNow ≤ 0 := by
  linarith

theorem adjacent_monotone_prefix_chains
    (e : ℕ → ℝ) (m N k n : ℕ)
    (hstep : ∀ r, m ≤ r → r < N → e (r+1) ≤ e r)
    (hm : m ≤ k) (hkn : k ≤ n) (hn : n ≤ N) : e n ≤ e k := by
  have hc : ∀ r, r ≤ N → k ≤ r → e r ≤ e k := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr hkr
      by_cases heq : r=k
      · simp [heq]
      · have hpred : k ≤ r-1 := by omega
        have hlt : r-1 < r := by omega
        have hp := ih (r-1) hlt (by omega) hpred
        have hs := hstep (r-1) (by omega) (by omega)
        have hid : r-1+1=r := by omega
        rw [hid] at hs
        exact le_trans hs hp
  exact hc n hn hkn

theorem nonnegative_prefix_removes_old_weak_guard
    (e : ℕ → ℝ) (m h N : ℕ)
    (hpositive : ∀ r, r ≤ N → 0 ≤ e r)
    (hearly : ∀ r, m ≤ r → r ≤ h → 0 ≤ e r → e (r+1) ≤ e r)
    (hlate : ∀ r, h ≤ r → r < N → e (r+1) ≤ e r) :
    ∀ r, m ≤ r → r < N → e (r+1) ≤ e r := by
  intro r hmr hrN
  by_cases hrh : r ≤ h
  · exact hearly r hmr hrh (hpositive r (by omega))
  · exact hlate r (by omega) hrN

theorem unbalanced_gap_covers_all_new_half
    (c b t n : ℕ) (hgap : b+t+3 ≤ c)
    (hhalf : 2*n ≤ c+b+t) : n+1 < c := by
  omega

#print axioms crossing_window_curvature_nonpositive
#print axioms adjacent_monotone_prefix_chains
#print axioms nonnegative_prefix_removes_old_weak_guard
#print axioms unbalanced_gap_covers_all_new_half

end AgentHalfLCWeakWindowTransport
