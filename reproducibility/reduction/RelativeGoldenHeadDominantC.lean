import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace RelativeGoldenHeadDominantC

def S (H : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ i ∈ Finset.Ico a b,H i

lemma split (H : ℕ → ℝ) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    S H a c=S H a b+S H b c := by
  exact (Finset.sum_Ico_consecutive H hab hbc).symm

theorem sixth_power_atom_budgets (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (heq : q^2+q=1) :
    0<q^6 ∧ q^6 ≤ q^2 ∧ q^6 ≤ 1-q ∧ q^6 ≤ 3*q^2-q ∧
    -q+q^2+2*q^4=q^6 := by
  have hqlo : 3/5<q := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ 3/5-q by linarith) (show 0 ≤ 3/5+q by linarith)
    nlinarith
  have h2 : q^2=1-q := by linarith
  have hc := congrArg (fun x : ℝ => x*q) heq
  have h3 : q^3=2*q-1 := by nlinarith
  have h4 : q^4=2-3*q := by
    calc
      q^4=(q^2)^2 := by ring
      _=(1-q)^2 := by rw [h2]
      _=2-3*q := by nlinarith
  have h6 : q^6=5-8*q := by
    calc
      q^6=(q^2)^3 := by ring
      _=(1-q)^3 := by rw [h2]
      _=5-8*q := by nlinarith
  refine ⟨pow_pos hq0 6,?_,?_,?_,?_⟩ <;> nlinarith

lemma head_nonnegative (H : ℕ → ℝ) (W a b : ℕ) (v : ℝ)
    (hv : 0 ≤ v) (hhead : ∀ i,2 ≤ i → i ≤ W → v ≤ H i)
    (ha : 2 ≤ a) (hb : b ≤ W+1) : 0 ≤ S H a b := by
  apply Finset.sum_nonneg
  intro i hi
  have hm := Finset.mem_Ico.mp hi
  exact le_trans hv (hhead i (by omega) (by omega))

theorem nonempty_head_interval_bound (H : ℕ → ℝ) (W a b : ℕ) (v : ℝ)
    (hv : 0 ≤ v) (hhead : ∀ i,2 ≤ i → i ≤ W → v ≤ H i)
    (ha : 2 ≤ a) (hab : a<b) (hb : b ≤ W+1) : v ≤ S H a b := by
  have hpoint : v ≤ H a := hhead a ha (by omega)
  apply le_trans hpoint
  apply Finset.single_le_sum
  · intro i hi
    have hm := Finset.mem_Ico.mp hi
    exact le_trans hv (hhead i (by omega) (by omega))
  · exact Finset.mem_Ico.mpr ⟨le_refl a,hab⟩

theorem complete_quantitative_head_tail_window
    (H : ℕ → ℝ) (W a b : ℕ) (q c rho rhonew : ℝ)
    (hW : 3 ≤ W) (haW : a ≤ W) (hab : a<b)
    (ha0 : a=0 → 2 ≤ b) (ha1 : a=1 → 4 ≤ b)
    (hc : 0 ≤ c) (hrho : 0 ≤ rho) (_hrhonew : 0 ≤ rhonew)
    (hrhocon : rhonew ≤ rho) (hrho1 : rho ≤ 1)
    (hcq : c ≤ q^2) (hc0 : c ≤ 1-q) (hc1 : c ≤ 3*q^2-q)
    (hc3 : c ≤ -q+q^2+2*q^4)
    (hhead : ∀ i,2 ≤ i → i ≤ W → c*rho ≤ H i)
    (h0 : H 0=1) (h1 : H 1=-q) (h2 : H 2=q^2) (h3 : H 3=2*q^2)
    (hWval : H W=rho)
    (htail : ∀ B,W<B → q^2*rho ≤ S H W B) : c*rhonew ≤ S H a b := by
  have hv : 0 ≤ c*rho := mul_nonneg hc hrho
  have htarget : c*rhonew ≤ c*rho := mul_le_mul_of_nonneg_left hrhocon hc
  have htargetc : c*rhonew ≤ c := by nlinarith [mul_nonneg hc (show 0 ≤ 1-rhonew by linarith)]
  have htailnn : ∀ B,W<B → 0 ≤ S H W B := by
    intro B hB
    exact le_trans (mul_nonneg (sq_nonneg q) hrho) (htail B hB)
  have hzero : ∀ B,2 ≤ B → B ≤ W+1 → 1-q ≤ S H 0 B := by
    intro B hB hBW
    have hs := split H 0 2 B (by omega) hB
    have hsmall : S H 0 2=1-q := by
      norm_num [S,Finset.sum_Ico_succ_top,Finset.sum_range_succ,h0,h1]; ring
    have hn := head_nonnegative H W 2 B (c*rho) hv hhead (le_refl 2) hBW
    linarith
  have hone : ∀ B,4 ≤ B → B ≤ W+1 → 3*q^2-q ≤ S H 1 B := by
    intro B hB hBW
    have hs := split H 1 4 B (by omega) hB
    have hsmall : S H 1 4=3*q^2-q := by
      norm_num [S,Finset.sum_Ico_succ_top,h1,h2,h3]; ring
    have hn := head_nonnegative H W 4 B (c*rho) hv hhead (by omega) hBW
    linarith
  by_cases hz : a=0
  · subst a
    by_cases hb : b ≤ W+1
    · exact le_trans htargetc (le_trans hc0 (hzero b (ha0 rfl) hb))
    · have hs := split H 0 W b (by omega) (by omega)
      have hh := hzero W (by omega) (by omega)
      have ht := htailnn b (by omega)
      linarith
  by_cases ho : a=1
  · subst a
    by_cases hb : b ≤ W+1
    · exact le_trans htargetc (le_trans hc1 (hone b (ha1 rfl) hb))
    · by_cases hW3 : W=3
      · subst W
        have hs := split H 1 3 b (by omega) (by omega)
        have hsmall : S H 1 3=-q+q^2 := by norm_num [S,Finset.sum_Ico_succ_top,h1,h2]
        have ht := htail b (by omega)
        have hrhoval : rho=2*q^2 := by linarith [hWval,h3]
        rw [hrhoval] at ht
        nlinarith
      · have hs := split H 1 W b (by omega) (by omega)
        have hh := hone W (by omega) (by omega)
        have ht := htailnn b (by omega)
        linarith
  have ha2 : 2 ≤ a := by omega
  by_cases hb : b ≤ W+1
  · exact le_trans htarget (nonempty_head_interval_bound H W a b (c*rho) hv hhead ha2 hab hb)
  · have hs := split H a W b haW (by omega)
    by_cases ha : a<W
    · have hh := nonempty_head_interval_bound H W a W (c*rho) hv hhead ha2 ha (by omega)
      have ht := htailnn b (by omega)
      linarith
    · have he : a=W := by omega
      subst a
      have ht := htail b (by omega)
      have hcb : c*rho ≤ q^2*rho := mul_le_mul_of_nonneg_right hcq hrho
      exact le_trans htarget (le_trans hcb ht)

theorem all_dominant_reference_read_guards (a t n : ℕ)
    (_ha : 3 ≤ a) (ht : 2*a ≤ t) (hn : t+4<n) (hend : n<a+t) :
    2 ≤ n-t-1 ∧ n-t-1 ≤ a ∧ a+7 ≤ n-1 := by omega

theorem dominant_deficit_and_small_count_mode
    (u h a r t ell : ℕ) (ha : 3 ≤ a) (hr : 1 ≤ r)
    (hid : h+r=a) (ht : 2*a ≤ t) (hell : 2*ell ≤ 3*u+a+r+1)
    (hcase : u<h ∨ u+r ≤ 5) : ell ≤ t+4 := by omega

theorem dominant_surplus_actual_read_guards (u h a r t n : ℕ)
    (_ha : 3 ≤ a) (hid : h+r=a) (hu : h ≤ u)
    (_ht : 2*a ≤ t) (hn : t+4<n) (hend : n<a+t) (hloss : u+r+2<n) :
    2 ≤ n-t-1 ∧ n-t-1 ≤ u+r+1 ∧ max a (u+r+2) ≤ n-1 := by omega

theorem strict_reference_tail_payment (q rho head tail : ℝ)
    (hhead : q^6*rho ≤ head) (htail : tail ≤ q^7*rho)
    (hq : 0<q) (hq1 : q<1) (hrho : 0<rho) : tail<head := by
  have hp := mul_pos (mul_pos (pow_pos hq 6) (show 0<1-q by linarith)) hrho
  have hid : q^6*rho-q^7*rho=q^6*(1-q)*rho := by ring
  linarith

theorem all_current_dominant_assembly (t W L ell : ℕ) (C : ℕ → Prop)
    (hprefix : ∀ n,n ≤ t+4 → C n) (hpost : ∀ n,ell<n → C n)
    (hlate : ∀ n,W ≤ n → C n) (hprotected : ∀ n,n ≤ L+1 → C n)
    (hcore : ∀ n,t+4<n → n<W → n ≤ ell → L+1<n → C n) : ∀ n,C n := by
  intro n
  by_cases hp : n ≤ t+4
  · exact hprefix n hp
  by_cases hm : ell<n
  · exact hpost n hm
  by_cases hl : W ≤ n
  · exact hlate n hl
  by_cases hs : n ≤ L+1
  · exact hprotected n hs
  exact hcore n (by omega) (by omega) (by omega) (by omega)

#print axioms sixth_power_atom_budgets
#print axioms nonempty_head_interval_bound
#print axioms complete_quantitative_head_tail_window
#print axioms all_dominant_reference_read_guards
#print axioms dominant_deficit_and_small_count_mode
#print axioms dominant_surplus_actual_read_guards
#print axioms strict_reference_tail_payment
#print axioms all_current_dominant_assembly

end RelativeGoldenHeadDominantC
