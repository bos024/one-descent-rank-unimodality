import Mathlib

namespace FirstMissingHooks

theorem sum_one_extra (s : Finset ℕ) (u : ℕ → ℤ) (i : ℕ)
    (hi : i ∈ s) (hpos : ∀ j ∈ s, 1 ≤ u j) (hextra : 2 ≤ u i) :
    (s.card:ℤ)+1 ≤ ∑ j ∈ s, u j := by
  have hn : ∀ j ∈ s, 0 ≤ u j-1 := by intro j hj;have h:=hpos j hj;omega
  have hsingle := Finset.single_le_sum hn hi
  have hid : (∑ j ∈ s, (u j-1)) = (∑ j ∈ s,u j)-(s.card:ℤ) := by
    rw [Finset.sum_sub_distrib]
    simp
  omega

theorem nonhook_first_bound (n k : ℕ) (u : ℕ → ℤ)
    (hsum : ∑ j ∈ Finset.range k,u j = (n:ℤ))
    (hpos : ∀ j, j < k → 1 ≤ u j)
    (hnonhook : ∃ i, i < k ∧ i ≠ 0 ∧ 2 ≤ u i) :
    u 0 ≤ (n:ℤ)-(k:ℤ) ∧ k+1 ≤ n := by
  obtain ⟨i,hi,hi0,hextra⟩ := hnonhook
  have h0 : 0 ∈ Finset.range k := by simp;omega
  have him : i ∈ Finset.range k := Finset.mem_range.mpr hi
  have hwhole := sum_one_extra (Finset.range k) u i him
    (fun j hj => hpos j (Finset.mem_range.mp hj)) hextra
  have hirest : i ∈ (Finset.range k).erase 0 := Finset.mem_erase.mpr ⟨hi0,him⟩
  have hrest := sum_one_extra ((Finset.range k).erase 0) u i hirest
    (fun j hj => hpos j (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)) hextra
  have hcard : ((Finset.range k).erase 0).card = k-1 := by
    rw [Finset.card_erase_of_mem h0]
    simp
  have he := Finset.sum_erase_add (Finset.range k) u h0
  simp only [Finset.card_range] at hwhole
  rw [hcard] at hrest
  omega

theorem positive_word_max (n k : ℕ) (u : ℕ → ℤ)
    (hsum : ∑ j ∈ Finset.range k,u j = (n:ℤ))
    (hpos : ∀ j, j < k → 1 ≤ u j) :
    ∀ i, i < k → u i ≤ (n:ℤ)-(k:ℤ)+1 := by
  intro i hi
  have him : i ∈ Finset.range k := Finset.mem_range.mpr hi
  have hcard : ((Finset.range k).erase i).card = k-1 := by
    rw [Finset.card_erase_of_mem him]
    simp
  have hlower : (((Finset.range k).erase i).card:ℤ)
      ≤ ∑ j ∈ (Finset.range k).erase i,u j := by
    calc
      _ = ∑ _j ∈ (Finset.range k).erase i,(1:ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hpos j (Finset.mem_range.mp (Finset.mem_erase.mp hj).2))
  have he := Finset.sum_erase_add (Finset.range k) u him
  rw [hcard] at hlower
  omega

theorem nonhook_right_alignment (n k : ℕ) (cap : ℤ) (u c : ℕ → ℤ)
    (hsum : ∑ j ∈ Finset.range k,u j = (n:ℤ))
    (hpos : ∀ j, j < k → 1 ≤ u j)
    (hcap : ∀ j, j < k → u j ≤ cap)
    (hnonhook : ∃ i, i < k ∧ i ≠ 0 ∧ 2 ≤ u i)
    (hstair : ∀ j, j < n-1 → min ((j:ℤ)+1) cap ≤ c j) :
    ∀ i, i < k → u i ≤ c (n-1-k+i) := by
  have hb := nonhook_first_bound n k u hsum hpos hnonhook
  have hm := positive_word_max n k u hsum hpos
  intro i hi
  have hidx : n-1-k+i<n-1 := by omega
  have hc := hstair (n-1-k+i) hidx
  have hu := hm i hi
  have hcu := hcap i hi
  by_cases hz : i=0
  · subst i
    omega
  · omega

#print axioms sum_one_extra
#print axioms nonhook_first_bound
#print axioms nonhook_right_alignment
end FirstMissingHooks
