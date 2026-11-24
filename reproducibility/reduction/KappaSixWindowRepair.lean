import Mathlib
set_option maxHeartbeats 2500000
namespace KappaSixWindowRepair

theorem one_part_compulsory_birth_only_exception (a k : ℕ)
    (ha : 3 ≤ a) (hk : 3 ≤ k) (hk6 : k ≤ 6) :
    (a=3 ∧ k=6) ∨ (k ≤ a+2 ∧ a+2-k ≤ a-1) := by omega

theorem exceptional_one_part_arm_unique (alpha t : ℕ)
    (ha : 1 ≤ alpha) (ht : 2 ≤ t) (h : alpha+t=3) :
    alpha=1 ∧ t=2 := by omega

theorem exact_exceptional_source_and_strict_mode_edge (y : ℝ)
    (hy0 : 1 ≤ y) (hy1 : y ≤ 31) :
    1 ≤ 2*34-(y+36) ∧ 34 < y+36 ∧
    2*17-34=(0:ℝ) ∧ 2*9-17=(1:ℝ) ∧ 2*5-9=(1:ℝ) ∧
    2*2-5=(-1:ℝ) ∧ 2*1-2=(0:ℝ) := by
  norm_num
  constructor <;> linarith

theorem whole_critical_three_rank_payment (E : ℕ → ℝ) (L t : ℕ)
    (ht : 3 ≤ t)
    (hprefix : ∀ j, j ≤ L → 1 ≤ E j)
    (hcritical : ∀ j, L < j → j ≤ L+3 → E j ≤ 1) :
    ∀ n, L < n → n ≤ L+3 → t ≤ n → E n-E (n-t) ≤ 0 := by
  intro n hn hn3 htn
  have hj : n-t ≤ L := by omega
  have h0 := hprefix (n-t) hj
  have h1 := hcritical n hn hn3
  linarith

theorem entire_clipped_window_tail_after_sign_cut
    (E W : ℕ → ℝ) (R t : ℕ)
    (hpos : ∀ n, n ≤ R → 0 ≤ E n)
    (hneg : ∀ n, R < n → E n ≤ 0)
    (hrec : ∀ n, W (n+1)-W n=E (n+1)-(if n+1<t then 0 else E (n+1-t)))
    (hfar : ∀ n, R+t ≤ n → W n ≤ 0) :
    ∀ n, R ≤ n → max 0 (W (n+1)) ≤ max 0 (W n) := by
  intro n hn
  have hi := hneg (n+1) (by omega)
  have he := hrec n
  by_cases ht0 : n+1<t
  · rw [ite_eq_left ht0] at he
    apply max_le_max_left
    linarith
  · rw [ite_eq_right ht0] at he
    by_cases hout : n+1-t ≤ R
    · have hp := hpos (n+1-t) hout
      apply max_le_max_left
      linarith
    · have hf := hfar (n+1) (by omega)
      rw [max_eq_left hf]
      exact le_max_left _ _

theorem complete_three_rank_patch_no_revival
    (f : ℕ → ℝ) (L t : ℕ)
    (hhead : ∀ i j, i<j → j<L → f (i+1)<f i → f (j+1) ≤ f j)
    (hinit : ∀ n, n+1<t → n+1 ≤ L+3 → f n ≤ f (n+1))
    (hpatch : ∀ n, L ≤ n → n<L+3 → t ≤ n+1 → f (n+1) ≤ f n)
    (htail : ∀ n, L+3 ≤ n → f (n+1) ≤ f n) :
    ∀ i j, i<j → f (i+1)<f i → f (j+1) ≤ f j := by
  intro i j hij hfall
  by_cases hj : j<L
  · exact hhead i j hij hj hfall
  · by_cases hj3 : L+3 ≤ j
    · exact htail j hj3
    · by_cases ht : t ≤ j+1
      · exact hpatch j (by omega) (by omega) ht
      · have hh := hinit i (by omega) (by omega)
        linarith

theorem complete_positive_window_patch_with_clipping
    (E W : ℕ → ℝ) (L t : ℕ) (ht : 3 ≤ t)
    (hhead : ∀ i j, i<j → j<L →
      max 0 (W (i+1)) < max 0 (W i) → max 0 (W (j+1)) ≤ max 0 (W j))
    (hpos : ∀ n, n ≤ L+3 → 0 ≤ E n)
    (hprefix : ∀ j, j ≤ L → 1 ≤ E j)
    (hcritical : ∀ j, L<j → j ≤ L+3 → E j ≤ 1)
    (hneg : ∀ n, L+3<n → E n ≤ 0)
    (hrec : ∀ n, W (n+1)-W n=E (n+1)-(if n+1<t then 0 else E (n+1-t)))
    (hfar : ∀ n, L+3+t ≤ n → W n ≤ 0) :
    ∀ i j, i<j → max 0 (W (i+1)) < max 0 (W i) →
      max 0 (W (j+1)) ≤ max 0 (W j) := by
  apply complete_three_rank_patch_no_revival (fun n => max 0 (W n)) L t hhead
  · intro n hn hn3
    have he := hrec n
    rw [ite_eq_left hn] at he
    have hp := hpos (n+1) hn3
    exact max_le_max_left 0 (by linarith)
  · intro n hn hn3 htn
    have he := hrec n
    rw [ite_eq_right (by omega : ¬n+1<t)] at he
    have hp := whole_critical_three_rank_payment E L t ht hprefix hcritical
      (n+1) (by omega) (by omega) htn
    exact max_le_max_left 0 (by linarith)
  · exact entire_clipped_window_tail_after_sign_cut E W (L+3) t hpos hneg hrec hfar

theorem finite_no_revival_has_whole_up_down_mode (f : ℕ → ℝ)
    (h0 : 0 < f 0) (hfinite : ∃ N, ∀ n, N ≤ n → f n=0)
    (hNR : ∀ i j, i<j → f (i+1)<f i → f (j+1) ≤ f j) :
    ∃ l, (∀ n, n<l → f n ≤ f (n+1)) ∧
      (∀ n, l ≤ n → f (n+1) ≤ f n) := by
  classical
  have hex : ∃ n, f (n+1)<f n := by
    by_contra h
    have hinc : ∀ n, f n ≤ f (n+1) := by
      intro n
      by_contra hh
      exact h ⟨n, by linarith⟩
    have hle : ∀ n, f 0 ≤ f n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact le_trans ih (hinc n)
    obtain ⟨N,hN⟩ := hfinite
    have he := hle N
    rw [hN N le_rfl] at he
    linarith
  let l := Nat.find hex
  have hfall : f (l+1)<f l := Nat.find_spec hex
  refine ⟨l, ?_, ?_⟩
  · intro n hn
    have hh : ¬f (n+1)<f n := Nat.find_min hex hn
    linarith
  · intro n hn
    by_cases he : n=l
    · subst n; exact le_of_lt hfall
    · exact hNR l n (by omega) hfall

theorem every_exceptional_heavier_legal_append_has_three_window
    (b t last : ℕ)
    (hb : 15 ≤ b)
    (hcase : (b ≤ 3+t) ∨ (5 ≤ last ∧ last ≤ t)) : 3 ≤ t := by omega

end KappaSixWindowRepair
#print axioms KappaSixWindowRepair.one_part_compulsory_birth_only_exception
#print axioms KappaSixWindowRepair.exceptional_one_part_arm_unique
#print axioms KappaSixWindowRepair.exact_exceptional_source_and_strict_mode_edge
#print axioms KappaSixWindowRepair.whole_critical_three_rank_payment
#print axioms KappaSixWindowRepair.entire_clipped_window_tail_after_sign_cut
#print axioms KappaSixWindowRepair.complete_three_rank_patch_no_revival
#print axioms KappaSixWindowRepair.complete_positive_window_patch_with_clipping
#print axioms KappaSixWindowRepair.finite_no_revival_has_whole_up_down_mode
#print axioms KappaSixWindowRepair.every_exceptional_heavier_legal_append_has_three_window
