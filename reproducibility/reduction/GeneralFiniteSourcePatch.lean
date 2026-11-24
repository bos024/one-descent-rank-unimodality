import KappaSixWindowRepair
set_option maxHeartbeats 2500000
namespace GeneralFiniteSourcePatch

theorem arbitrary_finite_patch_no_revival
    (f : ℕ → ℝ) (L R t : ℕ)
    (hhead : ∀ i j, i<j → j<L → f (i+1)<f i → f (j+1) ≤ f j)
    (hinit : ∀ n, n+1<t → n+1 ≤ R → f n ≤ f (n+1))
    (hpatch : ∀ n, L ≤ n → n<R → t<n+1 → f (n+1) ≤ f n)
    (htail : ∀ n, R ≤ n → f (n+1) ≤ f n) :
    ∀ i j, i<j → f (i+1)<f i → f (j+1) ≤ f j := by
  intro i j hij hfall
  by_cases hj : j<L
  · exact hhead i j hij hj hfall
  · by_cases hjR : R ≤ j
    · exact htail j hjR
    · by_cases ht : t<j+1
      · exact hpatch j (by omega) (by omega) ht
      · have hh := hinit i (by omega) (by omega)
        linarith

theorem whole_body_guarded_critical_payment
    (E : ℕ → ℝ) (L R B t : ℕ) (H : ℝ)
    (hbody : ∀ j, 1 ≤ j → j ≤ B → H ≤ E j)
    (hcritical : ∀ n, L<n → n ≤ R → E n ≤ H)
    (hreach : R ≤ t+B) :
    ∀ n, L<n → n ≤ R → t<n → E n-E (n-t) ≤ 0 := by
  intro n hn hnR htn
  have hj0 : 1 ≤ n-t := by omega
  have hj1 : n-t ≤ B := by omega
  have h0 := hbody (n-t) hj0 hj1
  have h1 := hcritical n hn hnR
  linarith

theorem entire_finite_window_patch_up_down
    (E W : ℕ → ℝ) (L R B t : ℕ) (H : ℝ)
    (hhead : ∀ i j, i<j → j<L →
      max 0 (W (i+1)) < max 0 (W i) → max 0 (W (j+1)) ≤ max 0 (W j))
    (hpos : ∀ n, n ≤ R → 0 ≤ E n)
    (hbody : ∀ j, 1 ≤ j → j ≤ B → H ≤ E j)
    (hcritical : ∀ n, L<n → n ≤ R → E n ≤ H)
    (hneg : ∀ n, R<n → E n ≤ 0)
    (hrec : ∀ n, W (n+1)-W n=E (n+1)-(if n+1<t then 0 else E (n+1-t)))
    (hfar : ∀ n, R+t ≤ n → W n ≤ 0)
    (hreach : R ≤ t+B) (h0 : 0 < W 0)
    (hfinite : ∃ N, ∀ n, N ≤ n → W n=0) :
    ∃ l, (∀ n, n<l → max 0 (W n) ≤ max 0 (W (n+1))) ∧
      (∀ n, l ≤ n → max 0 (W (n+1)) ≤ max 0 (W n)) := by
  have hNR : ∀ i j, i<j → max 0 (W (i+1)) < max 0 (W i) →
      max 0 (W (j+1)) ≤ max 0 (W j) := by
    apply arbitrary_finite_patch_no_revival (fun n => max 0 (W n)) L R t hhead
    · intro n hn hnR
      have he := hrec n
      rw [ite_eq_left hn] at he
      have hp := hpos (n+1) hnR
      exact max_le_max_left 0 (by linarith)
    · intro n hn hnR htn
      have he := hrec n
      rw [ite_eq_right (by omega : ¬n+1<t)] at he
      have hp := whole_body_guarded_critical_payment E L R B t H hbody hcritical hreach
        (n+1) (by omega) (by omega) htn
      exact max_le_max_left 0 (by linarith)
    · exact KappaSixWindowRepair.entire_clipped_window_tail_after_sign_cut E W R t hpos hneg hrec hfar
  apply KappaSixWindowRepair.finite_no_revival_has_whole_up_down_mode
    (fun n => max 0 (W n)) (by exact lt_max_of_lt_right h0) ?_ hNR
  obtain ⟨N,hN⟩ := hfinite
  refine ⟨N, ?_⟩
  intro n hn
  rw [hN n hn]
  norm_num

end GeneralFiniteSourcePatch
#print axioms GeneralFiniteSourcePatch.arbitrary_finite_patch_no_revival
#print axioms GeneralFiniteSourcePatch.whole_body_guarded_critical_payment
#print axioms GeneralFiniteSourcePatch.entire_finite_window_patch_up_down
