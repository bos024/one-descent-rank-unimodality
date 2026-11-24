import Mathlib
set_option maxHeartbeats 2500000
namespace FirstMissingProductMode
open Polynomial
noncomputable section

def Nonnegative (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n
def ordinaryFactor (U : ℝ[X]) : ℝ[X] := 1+X+2*X^2+X^3*U

theorem partial_coefficient_product_nonnegative (U D : ℝ[X]) (n : ℕ)
    (hU : Nonnegative U) (hD : ∀ j, j ≤ n → 0 ≤ D.coeff j) :
    0 ≤ (U*D).coeff n := by
  rw [coeff_mul]
  apply Finset.sum_nonneg
  intro x hx
  have he : x.1+x.2=n := by simpa using hx
  exact mul_nonneg (hU _) (hD _ (by omega))

theorem constant_term_pays_product_head (U D : ℝ[X]) (n : ℕ)
    (hU : Nonnegative U) (hU0 : 1 ≤ U.coeff 0)
    (hD : ∀ j, j ≤ n → 0 ≤ D.coeff j) :
    D.coeff n ≤ (U*D).coeff n := by
  have hh : U.coeff 0*D.coeff n ≤ (U*D).coeff n := by
    rw [coeff_mul]
    exact Finset.single_le_sum (fun (x : ℕ×ℕ) hx => by
      have he : x.1+x.2=n := by simpa using hx
      exact mul_nonneg (hU x.1) (hD x.2 (by omega)))
      (by simp : (0,n) ∈ Finset.HasAntidiagonal.antidiagonal n)
  have hm := mul_le_mul_of_nonneg_right hU0 (hD n le_rfl)
  linarith

theorem exact_complete_product_slope_identity (U Q : ℝ[X]) (n : ℕ) :
    ((1-X)*ordinaryFactor U*Q).coeff (n+3) =
      Q.coeff (n+3)+Q.coeff (n+1)-2*Q.coeff n+
        (U*((1-X)*Q)).coeff n := by
  have he : (1-X)*ordinaryFactor U*Q =
      Q+X^2*Q-X^3*(2*Q)+X^3*(U*((1-X)*Q)) := by
    dsimp [ordinaryFactor]
    ring_nf
  rw [he]
  have h2 : (X^2*Q).coeff (n+3)=Q.coeff (n+1) := by
    convert coeff_X_pow_mul Q 2 (n+1) using 1
  simp only [coeff_add,coeff_sub,coeff_X_pow_mul,h2]
  simp

theorem first_missing_dyadic_tail_dominates_its_index (k : ℕ) (hk : 6 ≤ k) :
    (k:ℝ) ≤ (2:ℝ)^(k-3) := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have he : k+1-3=(k-3)+1 := by omega
    rw [he,pow_succ]
    have hkR : (6:ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith only [ih,hkR]

theorem all_three_first_missing_product_slope_budgets
    (k : ℕ) (hk : 6 ≤ k) (delta y0 y1 y2 A0 A1 A2 : ℝ)
    (_hd0 : 0 ≤ delta) (hd1 : delta ≤ k)
    (hy0 : 0<y0) (hy1 : 0<y1) (hy2 : 0<y2)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : (2:ℝ)^(k-3) ≤ A2) :
    0<y0+A0 ∧ 0<y1+A1 ∧ 0<y2-delta+A2 := by
  have hp := first_missing_dyadic_tail_dominates_its_index k hk
  exact ⟨by linarith,by linarith,by linarith⟩

theorem complete_protected_first_missing_difference_prefix
    (Q : ℝ[X]) (k : ℕ) (_hk : 3 ≤ k) (h0 : Q.coeff 0=1)
    (hfull : ∀ j, 1 ≤ j → j<k → Q.coeff j=(2:ℝ)^(j-1)) :
    ∀ j, j<k → 0 ≤ ((1-X)*Q).coeff j := by
  intro j hj
  cases j with
  | zero => simp [sub_mul,h0]
  | succ j =>
    simp only [sub_mul,one_mul,coeff_sub,coeff_X_mul]
    rw [hfull (j+1) (by omega) hj]
    by_cases hj0 : j=0
    · subst j
      simp [h0]
    · rw [hfull j (by omega) (by omega)]
      have he : j+1-1=(j-1)+1 := by omega
      rw [he,pow_succ]
      nlinarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (j-1)]

theorem whole_first_missing_product_three_strict_increases
    (U Q : ℝ[X]) (k : ℕ) (delta : ℝ) (hk : 6 ≤ k)
    (hU : Nonnegative U) (hU0 : 1 ≤ U.coeff 0)
    (h0 : Q.coeff 0=1)
    (hfull : ∀ j, 1 ≤ j → j<k → Q.coeff j=(2:ℝ)^(j-1))
    (hdef : Q.coeff k=(2:ℝ)^(k-1)-delta) (hd : delta ≤ k)
    (hpos : ∀ j, k ≤ j → j ≤ k+2 → 0<Q.coeff j) :
    0<((1-X)*ordinaryFactor U*Q).coeff k ∧
    0<((1-X)*ordinaryFactor U*Q).coeff (k+1) ∧
    0<((1-X)*ordinaryFactor U*Q).coeff (k+2) := by
  let D : ℝ[X] := (1-X)*Q
  have hD := complete_protected_first_missing_difference_prefix Q k (by omega) h0 hfull
  have hp0 := partial_coefficient_product_nonnegative U D (k-3) hU
    (fun j hj => hD j (by omega))
  have hp1 := partial_coefficient_product_nonnegative U D (k-2) hU
    (fun j hj => hD j (by omega))
  have hp2 := constant_term_pays_product_head U D (k-1) hU hU0
    (fun j hj => hD j (by omega))
  have hpow0 : Q.coeff (k-2)=2*Q.coeff (k-3) := by
    rw [hfull (k-2) (by omega) (by omega),hfull (k-3) (by omega) (by omega)]
    have he : k-2-1=(k-3-1)+1 := by omega
    rw [he,pow_succ]
    ring_nf
  have hpow1 : Q.coeff (k-1)=2*Q.coeff (k-2) := by
    rw [hfull (k-1) (by omega) (by omega),hfull (k-2) (by omega) (by omega)]
    have he : k-1-1=(k-2-1)+1 := by omega
    rw [he,pow_succ]
    ring_nf
  have hcancel : Q.coeff k-2*Q.coeff (k-1) = -delta := by
    rw [hdef,hfull (k-1) (by omega) (by omega)]
    have he : k-1=(k-1-1)+1 := by omega
    have hp : (2:ℝ)^(k-1)=2*(2:ℝ)^(k-1-1) := by
      calc
        (2:ℝ)^(k-1)=(2:ℝ)^((k-1-1)+1) := congrArg (fun n => (2:ℝ)^n) he
        _=2*(2:ℝ)^(k-1-1) := by rw [pow_succ]; ring_nf
    linarith
  have hDlast : D.coeff (k-1)=(2:ℝ)^(k-3) := by
    dsimp [D]
    have hx : (X*Q).coeff (k-1)=Q.coeff (k-2) := by
      have hh := coeff_X_mul Q (k-2)
      have he : k-2+1=k-1 := by omega
      rw [he] at hh
      exact hh
    rw [sub_mul,one_mul,coeff_sub,hx]
    rw [hfull (k-1) (by omega) (by omega),hfull (k-2) (by omega) (by omega)]
    have he1 : k-1-1=(k-3)+1 := by omega
    have he2 : k-2-1=k-3 := by omega
    rw [he1,he2,pow_succ]
    ring_nf
  rw [hDlast] at hp2
  have he0 := exact_complete_product_slope_identity U Q (k-3)
  have he1 := exact_complete_product_slope_identity U Q (k-2)
  have he2 := exact_complete_product_slope_identity U Q (k-1)
  have hk03 : k-3+3=k := by omega
  have hk01 : k-3+1=k-2 := by omega
  have hk13 : k-2+3=k+1 := by omega
  have hk11 : k-2+1=k-1 := by omega
  have hk23 : k-1+3=k+2 := by omega
  have hk21 : k-1+1=k := by omega
  rw [hk03,hk01,hpow0] at he0
  rw [hk13,hk11,hpow1] at he1
  rw [hk23,hk21] at he2
  have hh := first_missing_dyadic_tail_dominates_its_index k hk
  have hy0 := hpos k le_rfl (by omega)
  have hy1 := hpos (k+1) (by omega) (by omega)
  have hy2 := hpos (k+2) (by omega) le_rfl
  change 0 ≤ (U*((1-X)*Q)).coeff (k-3) at hp0
  change 0 ≤ (U*((1-X)*Q)).coeff (k-2) at hp1
  change (2:ℝ)^(k-3) ≤ (U*((1-X)*Q)).coeff (k-1) at hp2
  exact ⟨by linarith,by linarith,by linarith⟩

theorem strict_forward_growth_places_every_ordinary_mode_after
    (H : ℕ → ℝ) (mu n : ℕ)
    (htail : ∀ j, mu ≤ j → H (j+1) ≤ H j)
    (h : H n<H (n+1)) : n+1 ≤ mu := by
  by_contra hh
  have hh1 := htail n (by omega)
  linarith

theorem arbitrary_one_part_exception_and_complete_window_geometry
    (alpha s k b t : ℕ) (ha : 1 ≤ alpha) (hs : 2 ≤ s)
    (hsmall : alpha+s+3 ≤ k) (hb : k ≤ b) (ht : k-3 ≤ t) :
    let a := alpha+s
    let m := min (alpha+1) s
    let L := b+a-k+1
    let R := b+m-1
    6 ≤ k ∧ 1 ≤ L ∧ 2 ≤ m ∧ m ≤ a-1 ∧ L<R ∧ R ≤ t+L := by
  dsimp
  have hm0 : 2 ≤ min (alpha+1) s := le_min (by omega) hs
  have hm1 := min_le_left (alpha+1) s
  have hm2 := min_le_right (alpha+1) s
  omega

theorem arbitrary_first_missing_birth_dichotomy (a k : ℕ)
    (ha : 3 ≤ a) (hk : 3 ≤ k) :
    (a+3 ≤ k) ∨ (0 ≤ a+2-k ∧ a+2-k ≤ a-1 ∧ k ≤ a+2) := by omega

#print axioms partial_coefficient_product_nonnegative
#print axioms constant_term_pays_product_head
#print axioms exact_complete_product_slope_identity
#print axioms first_missing_dyadic_tail_dominates_its_index
#print axioms all_three_first_missing_product_slope_budgets
#print axioms complete_protected_first_missing_difference_prefix
#print axioms whole_first_missing_product_three_strict_increases
#print axioms strict_forward_growth_places_every_ordinary_mode_after
#print axioms arbitrary_one_part_exception_and_complete_window_geometry
#print axioms arbitrary_first_missing_birth_dichotomy
end
end FirstMissingProductMode
