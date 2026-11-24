import Mathlib

namespace SourceCurvatureLinearOwner

theorem mirror_base_budget
    (r e L : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L) (hr : 3*e+6*L+5 ≤ r) :
    (r+e+3)*(r+e+2*L+2) ≤ 2*r*(r-2*L+1) := by
  let x := r-(3*e+6*L+5)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have heq : r=x+3*e+6*L+5 := by dsimp [x]; ring
  rw [heq]
  nlinarith [sq_nonneg x, sq_nonneg e, mul_nonneg hx he,
    mul_nonneg hx hL, mul_nonneg he hL]

theorem mirrored_ratio_pair
    (r e L i : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hr : 3*e+6*L+5 ≤ r) (hi : 0 ≤ i) (hj : 0 ≤ 2*L-1-i) :
    ((r+e+3+i)/(r-i))*((r+e+3+(2*L-1-i))/(r-(2*L-1-i))) ≤ 2 := by
  have hden1 : 0 < r-i := by linarith
  have hden2 : 0 < r-(2*L-1-i) := by linarith
  have hb := mirror_base_budget r e L he hL hr
  have hp := mul_nonneg hi hj
  have hn : (r+e+3+i)*(r+e+3+(2*L-1-i))
      ≤ 2*((r-i)*(r-(2*L-1-i))) := by nlinarith
  rw [div_mul_div_comm]
  exact (div_le_iff₀ (mul_pos hden1 hden2)).mpr hn

theorem full_paired_product
    (L : ℕ) (x : ℕ → ℝ) (hx : ∀ i<2*L, 0 ≤ x i)
    (hpair : ∀ i<L, x i*x (2*L-1-i) ≤ 2) :
    (∏ i∈Finset.range (2*L), x i) ≤ 2^L := by
  have hreflect : (∏ i∈Finset.range L, x (2*L-1-i)) =
      ∏ i∈Finset.range L, x (L+i) := by
    calc
      (∏ i∈Finset.range L, x (2*L-1-i))
          = ∏ i∈Finset.range L, x (L+(L-1-i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            have ht := Finset.mem_range.mp hi
            omega
      _ = ∏ i∈Finset.range L, x (L+i) :=
        Finset.prod_range_reflect (fun i => x (L+i)) L
  calc
    (∏ i∈Finset.range (2*L), x i)
        = (∏ i∈Finset.range L, x i)*(∏ i∈Finset.range L, x (L+i)) := by
          rw [show 2*L=L+L by omega]
          exact Finset.prod_range_add x L L
    _ = ∏ i∈Finset.range L, (x i*x (2*L-1-i)) := by
      rw [← hreflect, Finset.prod_mul_distrib]
    _ ≤ ∏ i∈Finset.range L, (2:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have ht := Finset.mem_range.mp hi
        exact mul_nonneg (hx i (by omega)) (hx (2*L-1-i) (by omega))
      · intro i hi
        exact hpair i (Finset.mem_range.mp hi)
    _ = 2^L := by simp

theorem degree_forces_both_payments
    (r e L d D : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hd : d=e+L+3) (hD : D=2*r+2+e) (hlarge : 12*d-24 ≤ D) :
    3*e+6*L+5 ≤ r ∧ 4*e+3 ≤ r := by constructor <;> linarith

theorem one_backward_step_payment
    (r e : ℝ) (he : 0 ≤ e) (hr : 2*e+3 ≤ r) :
    (e+1)*(r+e+3) ≤ (r+1)*r := by
  let x := r-(2*e+3)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have heq : r=x+2*e+3 := by dsimp [x]; ring
  rw [heq]
  nlinarith [sq_nonneg x, sq_nonneg e, mul_nonneg hx he]

theorem paired_curvature_payment
    (L : ℕ) (r e C f B : ℝ) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hB : 0 ≤ B) (hpow : (2:ℝ)^L=4*B) (hr : 4*e+3 ≤ r)
    (hcurve : (r+1)*C ≤ (e+1)*((2:ℝ)^L*f)) : C ≤ B*f := by
  have hR : 0 < r+1 := by linarith
  have hp := mul_nonneg (show 0 ≤ r+1-4*(e+1) by linarith) (mul_nonneg hB hf)
  rw [hpow] at hcurve
  have ht : (r+1)*C ≤ (r+1)*(B*f) := by nlinarith
  by_contra! hn
  have hz := mul_pos hR (sub_pos.mpr hn)
  nlinarith

theorem dyadic_offset_payment_scale (L : ℕ) (hL : 2 ≤ L) :
    (2:ℝ)^L=4*2^(L-2) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hL
  rw [hk]
  simp only [Nat.add_sub_cancel_left, pow_add]
  norm_num

theorem negative_index_linear_bound
    (D h d : ℤ) (hh : 2 ≤ h) (hd : 6 ≤ d) (hbirth : D+h+2-d < 0) :
    D ≤ 12*d-25 := by omega

theorem fixed_first_missing_linear_weight
    (a alpha d k : ℤ) (ha : 1 ≤ alpha) (hk : k=alpha+d)
    (hweight : a ≤ alpha+24*d-50) : a ≤ 24*k-73 := by omega

#print axioms mirror_base_budget
#print axioms mirrored_ratio_pair
#print axioms full_paired_product
#print axioms degree_forces_both_payments
#print axioms one_backward_step_payment
#print axioms paired_curvature_payment
#print axioms dyadic_offset_payment_scale
#print axioms negative_index_linear_bound
#print axioms fixed_first_missing_linear_weight

end SourceCurvatureLinearOwner
