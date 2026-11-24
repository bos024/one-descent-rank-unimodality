import Mathlib

set_option maxHeartbeats 0
namespace LongRectangleRepair

theorem first_defect_support (k c D : ℤ) (hk : 5 ≤ k)
    (hmass : k*(k-1) ≤ 2*c) (hD : D=c+1-k) : 2*k-4 ≤ D := by
  have hp : 0 ≤ (k-5)*(k-2) := mul_nonneg (by omega) (by omega)
  nlinarith

theorem linear_main_degree (k c g s b h m : ℤ)
    (hk : 5 ≤ k) (hmass : k*(k-1) ≤ 2*c)
    (hg : g ≤ k-2) (hband : 2 ≤ g+s+1) (hb : b=c+s)
    (hh : 2*h ≤ b-1) (hm : m=b-h) : k ≤ m := by
  have hp : 0 ≤ (k-5)*(k-2) := mul_nonneg (by omega) (by omega)
  have hc : 3*k-5 ≤ c := by nlinarith
  omega

theorem reflected_mass_indices (k D g h i : ℤ)
    (hD : 2*k-4 ≤ D) (hg : g ≤ k-2)
    (hh : 0 ≤ h ∧ h ≤ g) (hi : 1 ≤ i ∧ i ≤ h) :
    h ≤ h+g-i+1 ∧ h+g-i+1 ≤ D := by omega

theorem convolution_dominates_mass (e : ℤ → ℤ) (H : ℕ → ℤ)
    (h : ℕ) (L D : ℤ)
    (hH : ∀ i ∈ Finset.range (h+1), 0 ≤ H i)
    (he : ∀ r, 0 ≤ r → r ≤ D → 1 ≤ e r)
    (hL : (h:ℤ) ≤ L ∧ L ≤ D) :
    (∑ i ∈ Finset.range (h+1), H i) ≤
      ∑ i ∈ Finset.range (h+1), e (L-(i:ℤ))*H i := by
  apply Finset.sum_le_sum
  intro i hi
  have hih : (i:ℤ) ≤ (h:ℤ) := by
    have hh := Finset.mem_range.mp hi
    omega
  have hp := he (L-(i:ℤ)) (by omega) (by omega)
  nlinarith [hH i hi]

theorem mass_dominates_coefficient (H : ℕ → ℤ) (h j : ℕ)
    (hH : ∀ i ∈ Finset.range (h+1), 0 ≤ H i) (hj : j ≤ h) :
    H j ≤ ∑ i ∈ Finset.range (h+1), H i := by
  exact Finset.single_le_sum hH (Finset.mem_range.mpr (by omega))

theorem cdf_slope_concavity (L R H l r i mass : ℤ → ℤ)
    (n : ℤ)
    (hL : L (l n+1)-L (l n)=mass n)
    (hR : R (r n)-R (r n-1)=i n)
    (hleft : H n ≤ mass n) (hright : 0 ≤ i n) (hprev : 0 ≤ H (n-1)) :
    L (l n)-R (r n)+H n ≤
      L (l n+1)-R (r n-1)+H (n-1) := by omega

theorem correction_support_splice (W a A : ℤ → ℤ) (d g : ℤ)
    (hA : ∀ n, 0 ≤ n → n ≤ g → A n=W n+a n)
    (ha : ∀ n, 0 ≤ n → n ≤ g → 0 ≤ a n)
    (hazero : ∀ n, d<n → n ≤ g → a n=0)
    (hmono : ∀ i j, 0 ≤ i → i ≤ j → j ≤ d → A j ≤ A i)
    (hW : ∀ i j, 0 ≤ i → i<j → j ≤ g → W i<0 → W j ≤ 0)
    (i j : ℤ) (hi : 0 ≤ i) (hij : i<j) (hj : j ≤ g) (hneg : A i<0) :
    A j ≤ 0 := by
  by_cases hd : j ≤ d
  · have hh := hmono i j hi (by omega) hd
    omega
  · have hwi : W i<0 := by
      have hh := hA i hi (by omega)
      have hha := ha i hi (by omega)
      omega
    have hwj := hW i j hi hij hj hwi
    have hzero := hazero j (by omega) hj
    have haj := hA j (by omega) hj
    omega

theorem long_ones_window_indices (k c D g s h w i : ℤ)
    (hk : 5 ≤ k) (hg : g ≤ k-2) (hs : h ≤ s ∧ s ≤ g)
    (hw : w ≤ 2*h) (hi : 0 ≤ i ∧ i ≤ h) (hD : D=c+1-k) :
    D+h<c+i ∧ w-s+i-1<k+g := by omega

theorem long_last_window_indices (k c D g s h i : ℤ)
    (hk : 5 ≤ k) (hg : g ≤ k-2) (hs : h<s ∧ s ≤ g)
    (hi : 0 ≤ i ∧ i ≤ h) (hD : D=c+1-k) :
    D+h<c+i ∧ h-s+i<k+g ∧ c+i<c+s := by omega

open Polynomial
def nonnegative (p : Polynomial ℤ) : Prop := ∀ n, 0 ≤ p.coeff n

theorem nonnegative_mul {p q : Polynomial ℤ}
    (hp : nonnegative p) (hq : nonnegative q) : nonnegative (p*q) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x.1) (hq x.2))

theorem padding_kernel_append_nonnegative (W K : Polynomial ℤ)
    (hW : nonnegative W) (hK : nonnegative K)
    (hzero : (W*K).coeff 0=1) : nonnegative (1-X+X*W*K) := by
  have hp := nonnegative_mul hW hK
  have hminus : nonnegative (W*K-1) := by
    intro n
    rw [coeff_sub,coeff_one]
    by_cases hn : n=0
    · subst n; simp [hzero]
    · simp [hn]; exact hp n
  have heq : 1-X+X*W*K=1+X*(W*K-1) := by ring
  rw [heq]
  intro n
  rw [coeff_add]
  apply add_nonneg
  · simp only [coeff_one]; split_ifs <;> norm_num
  · cases n with
    | zero => simp
    | succ n => simpa using hminus n

#print axioms first_defect_support
#print axioms linear_main_degree
#print axioms reflected_mass_indices
#print axioms convolution_dominates_mass
#print axioms mass_dominates_coefficient
#print axioms cdf_slope_concavity
#print axioms correction_support_splice
#print axioms long_ones_window_indices
#print axioms long_last_window_indices
#print axioms padding_kernel_append_nonnegative
end LongRectangleRepair
