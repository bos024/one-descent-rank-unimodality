import Mathlib
set_option maxHeartbeats 2000000
namespace KappaEightWindowRepair

theorem complete_canonical_small_padding_and_negative_rank_cover
    (alpha first a : ℕ) (ha : 1 ≤ alpha) (ha3 : alpha<3)
    (hf : 2 ≤ first) (hfa : first-1 ≤ alpha) (hw : 5 ≤ a) :
    (alpha=1 ∨ alpha=2) ∧ 2 ≤ first ∧ first ≤ alpha+1 ∧
    (a=5 ∨ 8 ≤ a+2) := by omega

theorem small_three_part_only_positive_source_exceptions
    (delta eta : ℕ) (hd : 1 ≤ delta) (he : delta ≤ eta) :
    (delta<2 → delta=1) ∧ (eta<2 → delta=1 ∧ eta=1) := by omega

theorem complete_ten_exception_prefix_mode_and_body_budgets
    (y z delta eta zeta cover : ℝ)
    (hy0 : 1 ≤ y) (hy1 : y ≤ 127) (hz : 1 ≤ z)
    (hd : 1 ≤ delta) (he : delta ≤ eta) (hze : eta+1 ≤ zeta)
    (hc : 7 ≤ cover) :
    1 ≤ 128-y ∧ 136<y+144 ∧ 148<y+168 ∧ 154<y+180 ∧
    162<y+196 ∧ 166<y+204 ∧ 183<y+238 ∧ 175<y+222 ∧
    376<z+497 ∧ 833<z+1157 ∧ 777<z+1045 ∧
    2 ≤ delta+eta ∧ 5 ≤ zeta+eta+2 ∧ 5 ≤ zeta+3 ∧
    21 ≤ 2*(4+cover)-1 := by
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

theorem all_ten_exceptional_patch_read_guards (b t : ℕ)
    (hb : 28 ≤ b) (ht : 5 ≤ t) :
    b+1 ≤ t+(b-4) ∧ b+1 ≤ t+(b-3) ∧
    b+1 ≤ t+(b-2) ∧ b+2 ≤ t+(b-2) ∧
    b+1 ≤ t+(b-3) ∧ b+3 ≤ t+(b-1) ∧
    1 ≤ b-4 ∧ 1 ≤ b-3 ∧ 1 ≤ b-2 ∧ 1 ≤ b-1 := by omega

theorem every_new_exceptional_heavier_append_has_five_window
    (a b t last : ℕ) (hb : 28 ≤ b)
    (hcase : (a ≤ 8 ∧ b ≤ a+t) ∨ (7 ≤ last ∧ last ≤ t)) :
    5 ≤ t := by omega

end KappaEightWindowRepair
#print axioms KappaEightWindowRepair.complete_canonical_small_padding_and_negative_rank_cover
#print axioms KappaEightWindowRepair.small_three_part_only_positive_source_exceptions
#print axioms KappaEightWindowRepair.complete_ten_exception_prefix_mode_and_body_budgets
#print axioms KappaEightWindowRepair.all_ten_exceptional_patch_read_guards
#print axioms KappaEightWindowRepair.every_new_exceptional_heavier_append_has_five_window
