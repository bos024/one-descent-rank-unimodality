import Mathlib

namespace ForwardDSinglePlateau

theorem two_edge_span_is_strict
    (a b c : ℤ) (hab : a≤b) (hbc : b≤c)
    (hone : a<b ∨ b<c) : a<c := by omega

theorem strict_window_survives_unit_except_one_edge
    (enter leave before current : ℤ)
    (hwindow : 1≤enter-leave) (hid : current-before=enter-leave) : before<current := by omega

theorem height_from_one_possible_flat
    (D : ℕ → ℤ) (ell e : ℕ) (hell : 2≤ell) (hbase : 1≤D 2)
    (hstep : ∀ i, 3 ≤ i → i ≤ ell → D (i-1) ≤ D i ∧ (i ≠ e → D (i-1)+1 ≤ D i)) :
    (ell:ℤ)-2≤D ell := by
  have hstrong : ∀ n, 2≤n → n≤ell →
      (n:ℤ)-1-(if 3≤e ∧ e≤n then 1 else 0)≤D n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro htwo
        have he : ¬(3≤e ∧ e≤2) := by omega
        simpa [he] using hbase
    | succ k hk ih =>
        intro hke
        have hp := ih (by omega)
        have hs := hstep (k+1) (by omega) hke
        simp only [Nat.add_sub_cancel] at hs
        by_cases heq : k+1=e
        · have hold : ¬(3≤e ∧ e≤k) := by omega
          have hnew : 3≤e ∧ e≤k+1 := by omega
          simp only [ite_eq_right hold] at hp
          simp only [ite_eq_left hnew]
          have hmono := hs.1
          omega
        · have hstrict := hs.2 heq
          have hind : (3≤e ∧ e≤k+1) ↔ (3≤e ∧ e≤k) := by omega
          by_cases hold : 3≤e ∧ e≤k
          · have hnew := hind.mpr hold
            simp only [ite_eq_left hold] at hp
            simp only [ite_eq_left hnew]
            omega
          · have hnew : ¬(3≤e ∧ e≤k+1) := fun h => hold (hind.mp h)
            simp only [ite_eq_right hold] at hp
            simp only [ite_eq_right hnew]
            omega
  have hh := hstrong ell hell le_rfl
  split_ifs at hh <;> omega

theorem smaller_TC_peak_failure_region
    (n ell M B value : ℤ) (hheight : ell-2≤M)
    (hpay : M+n-ell-3≤value) (hpeak : M-1≤value)
    (hB : B≤35) (hfail : value<B) : n≤39 ∧ M≤35 := by omega

#print axioms two_edge_span_is_strict
#print axioms strict_window_survives_unit_except_one_edge
#print axioms height_from_one_possible_flat
#print axioms smaller_TC_peak_failure_region

end ForwardDSinglePlateau
