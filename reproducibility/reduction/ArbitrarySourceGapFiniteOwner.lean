import Mathlib

namespace ArbitrarySourceGapFiniteOwner

theorem product_budget
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S, 0 ≤ x i) (hs : ∑ i∈S, x i ≤ 1) :
    (1-∑ i∈S, x i) * ∏ i∈S, (1+x i) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hxa := hx a (Finset.mem_insert_self a S)
    have hxS : ∀ i∈S, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i∈S, x i := Finset.sum_nonneg hxS
    have hsum_le : ∑ i∈S, x i ≤ 1 := by
      rw [Finset.sum_insert ha] at hs
      linarith
    have hprod : 0 ≤ ∏ i∈S, (1+x i) :=
      Finset.prod_nonneg (fun i hi => by linarith [hxS i hi])
    have hc : (1-(x a+∑ i∈S, x i))*(1+x a) ≤ 1-∑ i∈S, x i := by
      nlinarith [mul_nonneg hxa hsum, sq_nonneg (x a)]
    have hp := mul_le_mul_of_nonneg_right hc hprod
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    calc
      (1-(x a+∑ i∈S, x i))*((1+x a)*∏ i∈S, (1+x i))
          = ((1-(x a+∑ i∈S, x i))*(1+x a)) * ∏ i∈S, (1+x i) := by ring
      _ ≤ (1-∑ i∈S, x i)*∏ i∈S, (1+x i) := hp
      _ ≤ 1 := ih hxS hsum_le

theorem linear_range_sum (L : ℕ) (e : ℝ) :
    (∑ i∈Finset.range L, (e+3+2*(i:ℝ))) = (L:ℝ)*(e+(L:ℝ)+2) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem backward_chain
    (L : ℕ) (f x : ℕ → ℝ)
    (hx : ∀ i<L, 0 ≤ x i)
    (hstep : ∀ i<L, f i ≤ (1+x i)*f (i+1)) :
    f 0 ≤ (∏ i∈Finset.range L, (1+x i))*f L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp : 0 ≤ ∏ i∈Finset.range L, (1+x i) :=
      Finset.prod_nonneg (fun i hi => by
        have ht := hx i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
        linarith)
    have hi := ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))
      (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    calc
      f 0 ≤ (∏ i∈Finset.range L, (1+x i))*f L := hi
      _ ≤ (∏ i∈Finset.range L, (1+x i))*((1+x L)*f (L+1)) :=
        mul_le_mul_of_nonneg_left (hstep L (Nat.lt_succ_self L)) hp
      _ = (∏ i∈Finset.range (L+1), (1+x i))*f (L+1) := by
        rw [Finset.prod_range_succ]
        ring

theorem aggregate_ratio_budget
    (L : ℕ) (r e : ℝ) (x : ℕ → ℝ)
    (hx : ∀ i<L, 0 ≤ x i)
    (hstep : ∀ i<L, (r-(i:ℝ))*x i ≤ e+3+2*(i:ℝ)) :
    (r-(L:ℝ)+1)*(∑ i∈Finset.range L, x i)
      ≤ (L:ℝ)*(e+(L:ℝ)+2) := by
  rw [← linear_range_sum L e, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hxi := hx i (Finset.mem_range.mp hi)
  have hiN : i+1 ≤ L := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hiR : (i:ℝ)+1 ≤ (L:ℝ) := by exact_mod_cast hiN
  have hp := mul_nonneg (show 0 ≤ (L:ℝ)-(i:ℝ)-1 by linarith) hxi
  nlinarith [hstep i (Finset.mem_range.mp hi)]

theorem rational_budget_pays
    (r e l S P : ℝ) (he : 0 ≤ e) (hl : 0 ≤ l) (hP : 0 ≤ P)
    (hr : (e+l+3)*l+e ≤ r)
    (hS : (r-l+1)*S ≤ l*(e+l+2))
    (hprod : (1-S)*P ≤ 1) : (e+1)*P ≤ r+1 := by
  have hrl : l ≤ r := by
    have hp := mul_nonneg (show 0 ≤ e+l+2 by linarith) hl
    nlinarith
  have hB : 0 < r-l+1 := by linarith
  have hnorm : e+1 ≤ (r-l+1)*(1-S) := by nlinarith
  have hpositive : 0 ≤ 1-S := by
    by_contra! hn
    have hp := mul_neg_of_pos_of_neg hB hn
    linarith
  have hnorm2 : e+1 ≤ (r+1)*(1-S) := by
    have hp := mul_nonneg hl hpositive
    nlinarith
  have hp := mul_le_mul_of_nonneg_right hnorm2 hP
  have ht := mul_le_mul_of_nonneg_left hprod (show 0 ≤ r+1 by linarith)
  nlinarith

theorem arbitrary_gap_backward_payment
    (L : ℕ) (r e C : ℝ) (f x : ℕ → ℝ)
    (he : 0 ≤ e) (hfinal : 0 ≤ f L)
    (hr : (e+(L:ℝ)+3)*(L:ℝ)+e ≤ r)
    (hx : ∀ i<L, 0 ≤ x i)
    (hratio : ∀ i<L, (r-(i:ℝ))*x i ≤ e+3+2*(i:ℝ))
    (hstep : ∀ i<L, f i ≤ (1+x i)*f (i+1))
    (hcurve : (r+1)*C ≤ (e+1)*f 0) : C ≤ f L := by
  let S := ∑ i∈Finset.range L, x i
  let P := ∏ i∈Finset.range L, (1+x i)
  have hl : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i hi => by
    have ht := hx i (Finset.mem_range.mp hi)
    linarith)
  have hSbound : (r-(L:ℝ)+1)*S ≤ (L:ℝ)*(e+(L:ℝ)+2) :=
    aggregate_ratio_budget L r e x hx hratio
  have hS : S ≤ 1 := by
    have hrl : (L:ℝ) ≤ r := by
      have hp := mul_nonneg (show 0 ≤ e+(L:ℝ)+2 by linarith) hl
      nlinarith
    have hB : 0 < r-(L:ℝ)+1 := by linarith
    have hp : e+1 ≤ (r-(L:ℝ)+1)*(1-S) := by nlinarith
    by_contra! hn
    have ht := mul_neg_of_pos_of_neg hB (show 1-S<0 by linarith)
    linarith
  have hprod : (1-S)*P ≤ 1 := product_budget (Finset.range L) x
    (fun i hi => hx i (Finset.mem_range.mp hi)) hS
  have hfactor : (e+1)*P ≤ r+1 :=
    rational_budget_pays r e (L:ℝ) S P he hl hP hr hSbound hprod
  have hchain := backward_chain L f x hx hstep
  have hp := mul_le_mul_of_nonneg_left hchain (show 0 ≤ e+1 by linarith)
  have ht := mul_le_mul_of_nonneg_right hfactor hfinal
  have hrl : (L:ℝ) ≤ r := by
    have hz := mul_nonneg (show 0 ≤ e+(L:ℝ)+2 by linarith) hl
    nlinarith
  have hR : 0 < r+1 := by linarith
  have hpaid : (r+1)*C ≤ (r+1)*f L := by nlinarith
  by_contra! hn
  have hz := mul_pos hR (sub_pos.mpr hn)
  nlinarith

theorem integer_positive_recovery_finite_owner
    (r e d D : ℤ) (he : 0 ≤ e) (hd : 3 ≤ d)
    (hD : D=2*r+2+e) (hfail : r+(d-1)*e < d*(d-3)) :
    D ≤ 2*d*(d-3) := by
  have hr : r+(d-1)*e ≤ d*(d-3)-1 := by omega
  have hp := mul_nonneg (show 0 ≤ 2*d-3 by omega) he
  nlinarith

theorem integer_owner_weight_bound
    (a alpha h D d j : ℤ) (hD : D ≤ 2*d*(d-3))
    (hh : h ≤ D) (ha : a=alpha+D+h) (hj : j ≤ a+1) :
    a ≤ alpha+4*d*(d-3) ∧ j ≤ alpha+4*d*(d-3)+1 := by
  constructor <;> nlinarith

theorem negative_reverse_index_finite_owner
    (D h d : ℤ) (hh : 2 ≤ h) (hd : 3 ≤ d) (hbirth : D+h+2-d < 0) :
    D ≤ 2*d*(d-3) := by
  have hp := mul_nonneg (show 0 ≤ d-3 by omega) (show 0 ≤ 2*d-1 by omega)
  nlinarith

theorem fixed_first_missing_owner_weight
    (a alpha d k : ℤ) (hd : 6 ≤ d) (ha : 1 ≤ alpha) (hk : k=alpha+d)
    (hweight : a ≤ alpha+4*d*(d-3)) :
    a ≤ 1+4*(k-1)*(k-4) := by
  have hp := mul_nonneg (show 0 ≤ k-1-d by omega)
    (show 0 ≤ 4*(k-1+d)-13 by omega)
  nlinarith

theorem universal_count_head_threshold
    (g j K : ℤ) (hfloor : 5*(K-1) ≤ 2*g+1) (hceil : 2*g+1 < 5*K)
    (hcount : 5*j+4 ≤ 2*g) : j+2 ≤ K := by omega

theorem binary_mass_three_steps (u K : ℕ) (hK : u+3 ≤ K) :
    5*(2:ℕ)^u ≤ 2^K := by
  calc
    5*(2:ℕ)^u ≤ 2^(u+3) := by rw [pow_add]; norm_num; omega
    _ ≤ 2^K := by gcongr

#print axioms product_budget
#print axioms linear_range_sum
#print axioms backward_chain
#print axioms aggregate_ratio_budget
#print axioms rational_budget_pays
#print axioms arbitrary_gap_backward_payment
#print axioms integer_positive_recovery_finite_owner
#print axioms integer_owner_weight_bound
#print axioms negative_reverse_index_finite_owner
#print axioms fixed_first_missing_owner_weight
#print axioms universal_count_head_threshold
#print axioms binary_mass_three_steps

end ArbitrarySourceGapFiniteOwner
