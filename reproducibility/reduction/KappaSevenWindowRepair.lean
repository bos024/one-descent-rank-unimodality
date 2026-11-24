import Mathlib
set_option maxHeartbeats 2000000
namespace KappaSevenWindowRepair

theorem complete_small_owner_degree_and_one_part_cover (a l t : ℕ)
    (ha : 3 ≤ a) (hl : 2 ≤ l) (hlt : l ≤ t)
    (hD : (2-1)+(l-1)+(t-1) ≤ 36) :
    (a=3 ∨ a=4 ∨ 7 ≤ a+2) ∧ l+t ≤ 37 ∧ l ≤ 18 ∧ t ≤ 35 := by omega

theorem sole_binary_three_positive_exception (delta eta : ℕ)
    (hd : 1 ≤ delta) (he : delta ≤ eta) (hcurv : eta < 2) :
    delta=1 ∧ eta=1 := by omega

theorem complete_four_exception_prefix_mode_and_body_budgets
    (y z delta eta zeta cover : ℝ)
    (hy0 : 1 ≤ y) (hy1 : y ≤ 63) (hz : 1 ≤ z)
    (hd : 1 ≤ delta) (he : delta ≤ eta) (hze : eta+1 ≤ zeta)
    (hc : 6 ≤ cover) :
    1 ≤ 64-y ∧ 68 < y+72 ∧ 74 < y+84 ∧ 83 < y+102 ∧
    373 < z+493 ∧ 2 ≤ delta+eta ∧ 5 ≤ zeta+3 ∧
    19 ≤ 2*(4+cover)-1 := by
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith⟩

theorem all_four_exceptional_patch_read_guards (b t : ℕ)
    (hb : 21 ≤ b) (ht : 4 ≤ t) :
    b+1 ≤ t+(b-3) ∧ b+2 ≤ t+(b-2) ∧
    b+2 ≤ t+(b-1) ∧
    b-3 < b+1 ∧ b-2 < b+2 ∧ b-1 < b+2 ∧
    1 ≤ b-3 ∧ 1 ≤ b-2 ∧ 1 ≤ b-1 := by omega

theorem every_new_exceptional_heavier_append_has_four_window
    (a b t last : ℕ) (hb : 21 ≤ b)
    (hcase : (a ≤ 7 ∧ b ≤ a+t) ∨ (6 ≤ last ∧ last ≤ t)) :
    4 ≤ t := by omega

end KappaSevenWindowRepair
#print axioms KappaSevenWindowRepair.complete_small_owner_degree_and_one_part_cover
#print axioms KappaSevenWindowRepair.sole_binary_three_positive_exception
#print axioms KappaSevenWindowRepair.complete_four_exception_prefix_mode_and_body_budgets
#print axioms KappaSevenWindowRepair.all_four_exceptional_patch_read_guards
#print axioms KappaSevenWindowRepair.every_new_exceptional_heavier_append_has_four_window
