import Mathlib

namespace SourcePrefixFreeFirstHeight

theorem maximal_scope_late_layer_and_terminal_exclusion
    (a b j n S : ℤ) (hn : n=a+b-j)
    (hshort : j ≤ b) (hhalf : 2*j ≤ a+b+2)
    (hcenter : S ≤ a+b-1) :
    S ≤ 2*n+1 ∧ a < n+1 := by omega

theorem exact_first_birth_index (a b j k : ℤ) :
    (a+b-j)-(b+1-k) = a-j+k-1 := by ring

theorem later_layer_terminal_exclusion
    (a b j n k L left right : ℤ) (hn : n=a+b-j)
    (hright : right=b+1-k-L) (hcenter : left+right ≤ b-1)
    (hguard : k+L-2 ≤ b-j) :
    a+1 ≤ n+1-left ∧ n-right=a-j+k-1+L := by
  constructor <;> omega

theorem source_drop_pays_curvature
    (T C drop birth : ℝ) (hidentity : T=C-drop) (hpaid : birth ≤ drop) :
    T ≤ C-birth := by linarith

theorem one_nonnegative_component_pays
    {ι : Type*} (S : Finset ι) (drop : ι → ℝ) (i : ι) (birth : ℝ)
    (hi : i∈S) (hdrop : ∀ j∈S, 0 ≤ drop j) (hbirth : birth ≤ drop i) :
    birth ≤ ∑ j∈S, drop j := by
  exact le_trans hbirth (Finset.single_le_sum hdrop hi)

theorem heavier_owner_shift_budget
    (a b h m k : ℤ) (hk : 2 ≤ k)
    (huniversal : k*(k-1) ≤ 2*b) (hheavy : b ≤ a)
    (hcount : 2*h ≤ a-1) (hm : m=a-h) :
    (k-2)^2 ≤ 4*m := by nlinarith

theorem conditional_second_birth_pays
    (T C first second last : ℝ)
    (hfirst : T ≤ C-first) (htwo : T ≤ C-first-second)
    (hreplacement : first < C → last ≤ second)
    (hbudget : C ≤ first+last) : T ≤ 0 := by
  by_cases hpaid : C ≤ first
  · linarith
  · have hreplace := hreplacement (by linarith)
    linarith

theorem window_positive_curvature_le_entering
    (before leave previous entering C : ℝ)
    (hprev : 0 ≤ previous) (hwindow : before ≤ previous)
    (hcurve : C=(entering-previous)-(leave-before)) (hC : 0 < C)
    (hfall : leave < before → previous ≤ leave)
    (hrise : previous < entering → before ≤ leave) : C ≤ entering := by
  have henter : previous < entering := by
    by_contra! hn
    have hnegative : leave < before := by linarith
    have hafter := hfall hnegative
    linarith
  have hearlier := hrise henter
  linarith

theorem interval_contains_entering
    (t delta : ℕ) (r : ℤ) (Q : ℤ → ℝ)
    (hdelta : 1 ≤ delta) (ht : delta ≤ t) (hQ : ∀ i, 0 ≤ Q i) :
    Q (r+1) ≤ ∑ i∈Finset.range t, Q (r+(delta:ℤ)-(i:ℤ)) := by
  have hmem : delta-1 ∈ Finset.range t := by simp; omega
  have hindex : r+(delta:ℤ)-((delta-1:ℕ):ℤ)=r+1 := by omega
  have hsum := Finset.single_le_sum
    (s := Finset.range t) (f := fun i : ℕ => Q (r+(delta:ℤ)-(i:ℤ)))
    (fun i hi => hQ _) hmem
  simpa only [hindex] using hsum

theorem first_half_beyond_opposite_equal_boundary
    (a b j : ℤ) (hab : a ≤ b) (hhalf : 2*j ≤ a+b+2) (hafter : b < j) :
    a=b ∧ j=a+1 := by omega

theorem equal_weight_first_source_is_interior
    (a g k : ℤ) (ha : 3 ≤ a) (_hg : 1 ≤ g)
    (hcount : 2*g ≤ a-1) (hk : 3 ≤ k) (hupper : k ≤ g+2) :
    1 ≤ k-2 ∧ k-2 ≤ a-2 := by omega

theorem unit_curvature_paid_by_second_interior_height
    (T drop interior : ℝ) (hidentity : T=1-drop)
    (hdrop : interior-1 ≤ drop) (hinterior : 2 ≤ interior) : T ≤ 0 := by
  linarith

#print axioms maximal_scope_late_layer_and_terminal_exclusion
#print axioms exact_first_birth_index
#print axioms later_layer_terminal_exclusion
#print axioms source_drop_pays_curvature
#print axioms one_nonnegative_component_pays
#print axioms heavier_owner_shift_budget
#print axioms conditional_second_birth_pays
#print axioms window_positive_curvature_le_entering
#print axioms interval_contains_entering
#print axioms first_half_beyond_opposite_equal_boundary
#print axioms equal_weight_first_source_is_interior
#print axioms unit_curvature_paid_by_second_interior_height

end SourcePrefixFreeFirstHeight
