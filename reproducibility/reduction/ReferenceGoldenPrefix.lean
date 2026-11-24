import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

namespace ReferenceGoldenPrefix

def S (H : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ i ∈ Finset.Ico a b,H i

theorem interval_split (H : ℕ → ℝ) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    S H a c=S H a b+S H b c := by
  exact (Finset.sum_Ico_consecutive H hab hbc).symm

theorem positive_golden_atom_budgets (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 5/8)
    (heq : q^2+q=1) :
    0 < 1-q ∧ 0 < 3*q^2-q ∧ 0 < -q+q^2+2*q^4 := by
  have hqs : q < 5/8 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ q-5/8 by linarith) (show 0 ≤ q+5/8 by linarith)
    nlinarith
  have h2 : q^2=1-q := by linarith
  have h4 : q^4=2-3*q := by
    calc
      q^4=(q^2)^2 := by ring
      _=(1-q)^2 := by rw [h2]
      _=2-3*q := by nlinarith
  constructor
  · linarith
  constructor <;> nlinarith

theorem head_interval_nonnegative (H : ℕ → ℝ) (W a b : ℕ)
    (hhead : ∀ i,2 ≤ i → i ≤ W → 0 < H i) (ha : 2 ≤ a) (hb : b ≤ W+1) :
    0 ≤ S H a b := by
  apply Finset.sum_nonneg
  intro i hi
  have hm := Finset.mem_Ico.mp hi
  exact le_of_lt (hhead i (by omega) (by omega))

theorem head_interval_positive (H : ℕ → ℝ) (W a b : ℕ)
    (hhead : ∀ i,2 ≤ i → i ≤ W → 0 < H i) (ha : 2 ≤ a)
    (hab : a < b) (hb : b ≤ W+1) :
    0 < S H a b := by
  apply Finset.sum_pos'
  · intro i hi
    have hm := Finset.mem_Ico.mp hi
    exact le_of_lt (hhead i (by omega) (by omega))
  · refine ⟨a,?_,hhead a ha (by omega)⟩
    exact Finset.mem_Ico.mpr ⟨le_rfl,hab⟩

theorem zero_head_interval_positive (H : ℕ → ℝ) (W b : ℕ) (q : ℝ)
    (hhead : ∀ i,2 ≤ i → i ≤ W → 0 < H i)
    (h0 : H 0=1) (h1 : H 1=-q) (hq : q < 1)
    (hb0 : 2 ≤ b) (hb : b ≤ W+1) :
    0 < S H 0 b := by
  have hsmall : S H 0 2=1-q := by norm_num [S,Finset.sum_Ico_succ_top,Finset.sum_range_succ,h0,h1]; ring
  have hs := interval_split H 0 2 b (by omega) hb0
  have hp := head_interval_nonnegative H W 2 b hhead (le_refl 2) hb
  linarith

theorem one_head_interval_positive (H : ℕ → ℝ) (W b : ℕ) (q : ℝ)
    (hhead : ∀ i,2 ≤ i → i ≤ W → 0 < H i)
    (h1 : H 1=-q) (h2 : H 2=q^2) (h3 : H 3=2*q^2)
    (hq : 0 < 3*q^2-q) (hb0 : 4 ≤ b) (hb : b ≤ W+1) :
    0 < S H 1 b := by
  have hsmall : S H 1 4=3*q^2-q := by norm_num [S,Finset.sum_Ico_succ_top,h1,h2,h3]; ring
  have hs := interval_split H 1 4 b (by omega) hb0
  have hp := head_interval_nonnegative H W 4 b hhead (by omega) hb
  linarith

theorem complete_head_plus_alternating_tail_window (H : ℕ → ℝ) (W a b : ℕ) (q : ℝ)
    (hW : 3 ≤ W) (haW : a ≤ W) (hab : a < b)
    (ha0 : a=0 → 2 ≤ b) (ha1 : a=1 → 4 ≤ b)
    (hhead : ∀ i,2 ≤ i → i ≤ W → 0 < H i)
    (h0 : H 0=1) (h1 : H 1=-q) (h2 : H 2=q^2) (h3 : H 3=2*q^2)
    (hq0 : 0 < q) (hq : q < 1) (hq3 : 0 < 3*q^2-q)
    (hq6 : 0 < -q+q^2+2*q^4)
    (htail : ∀ B,W < B → q^2*H W ≤ S H W B) :
    0 < S H a b := by
  have hHW := hhead W (by omega) (le_refl W)
  have htailpos : ∀ B,W < B → 0 < S H W B := by
    intro B hB
    have hp := mul_pos (sq_pos_of_pos hq0) hHW
    linarith [htail B hB]
  by_cases hz : a=0
  · subst a
    by_cases hb : b ≤ W+1
    · exact zero_head_interval_positive H W b q hhead h0 h1 hq (ha0 rfl) hb
    · have hs := interval_split H 0 W b (by omega) (by omega)
      have hh := zero_head_interval_positive H W W q hhead h0 h1 hq (by omega) (by omega)
      have ht := htailpos b (by omega)
      linarith
  by_cases ho : a=1
  · subst a
    by_cases hb : b ≤ W+1
    · exact one_head_interval_positive H W b q hhead h1 h2 h3 hq3 (ha1 rfl) hb
    · by_cases hW3 : W=3
      · subst W
        have hs := interval_split H 1 3 b (by omega) (by omega)
        have hsmall : S H 1 3=-q+q^2 := by norm_num [S,Finset.sum_Ico_succ_top,h1,h2]
        have ht := htail b (by omega)
        rw [h3] at ht
        nlinarith
      · have hs := interval_split H 1 W b (by omega) (by omega)
        have hh := one_head_interval_positive H W W q hhead h1 h2 h3 hq3 (by omega) (by omega)
        have ht := htailpos b (by omega)
        linarith
  have ha2 : 2 ≤ a := by omega
  by_cases hb : b ≤ W+1
  · exact head_interval_positive H W a b hhead ha2 hab hb
  · have hs := interval_split H a W b haW (by omega)
    have hh := head_interval_nonnegative H W a W hhead ha2 (by omega)
    have ht := htailpos b (by omega)
    linarith

theorem all_current_window_geometry (W t n : ℕ) (ht : 3 ≤ t) (hn : 2 ≤ n)
    (hnW : n ≤ W+t) :
    n-t ≤ W ∧ n-t < n ∧ (n-t=0 → 2 ≤ n) ∧ (n-t=1 → 4 ≤ n) := by omega

theorem generic_ordinary_tilt_seed (a lam mu K H R : ℝ)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hlam : lam ≤ 2) (hmu : mu=a*lam)
    (hmu1 : 1 ≤ mu) (hK : 0 < K) (hH : 0 < H) (hR : 0 ≤ R) :
    0 < K*H+(1-a)*(1+a-mu+R)+(a^2-1)*(1-mu) := by
  have h1 : 0 ≤ 1+a-mu+R := by
    have hp := mul_nonneg (le_of_lt ha0) (show 0 ≤ 2-lam by linarith)
    nlinarith
  have h2 := mul_nonneg (show 0 ≤ 1-a by linarith) h1
  have h3 := mul_nonneg (show 0 ≤ 1-a^2 by nlinarith [sq_nonneg (1-a)]) (show 0 ≤ mu-1 by linarith)
  have hpos := mul_pos hK hH
  nlinarith

#print axioms interval_split
#print axioms positive_golden_atom_budgets
#print axioms head_interval_nonnegative
#print axioms head_interval_positive
#print axioms zero_head_interval_positive
#print axioms one_head_interval_positive
#print axioms complete_head_plus_alternating_tail_window
#print axioms all_current_window_geometry
#print axioms generic_ordinary_tilt_seed

end ReferenceGoldenPrefix

