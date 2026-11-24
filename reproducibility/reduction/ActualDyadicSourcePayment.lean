import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ActualDyadicSourcePayment
noncomputable section

theorem whole_indexed_owner_raw_gap (h r j : ℕ) (Q x y : ℝ)
    (hh : 2 ≤ h) (hx : 0 ≤ x) (hprev : y ≤ x)
    (hweight : 2*h+1 ≤ j+r) (hcenter : h+r+3 ≤ j)
    (hHilbert : ((r:ℝ)+1)*Q ≤ ((h:ℝ)+(r:ℝ)+1)*x)
    (hzero : r=0 → x=1 ∧ y=0 ∧ Q=(h:ℝ)+1)
    (hone : r=1 → x=(h:ℝ)+1 ∧ y=1 ∧ 2*Q ≤ ((h:ℝ)+1)*((h:ℝ)+2)) :
    4*Q ≤ ((j:ℝ)+1)*(2*x-y) := by
  by_cases hr0 : r=0
  · obtain ⟨hxx,hyy,hQQ⟩ := hzero hr0
    subst r
    have hw : (2:ℝ)*(h:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hweight
    rw [hxx,hyy,hQQ]
    nlinarith
  by_cases hr1 : r=1
  · obtain ⟨hxx,hyy,hQQ⟩ := hone hr1
    subst r
    have hwN : 2*h ≤ j := by omega
    have hw : (2:ℝ)*(h:ℝ) ≤ (j:ℝ) := by exact_mod_cast hwN
    have hhR : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have hsquare : 0 ≤ ((h:ℝ)-2)*(h:ℝ) := mul_nonneg (by linarith) (by positivity)
    have hprod := mul_le_mul_of_nonneg_right (show (2:ℝ)*(h:ℝ)+1 ≤ (j:ℝ)+1 by linarith)
      (show 0 ≤ (2:ℝ)*(h:ℝ)+1 by positivity)
    rw [hxx,hyy]
    nlinarith
  have hr2 : 2 ≤ r := by omega
  have hratioN : 4*(h+r+1) ≤ (j+1)*(r+1) := by
    by_cases heq : r=2
    · subst r
      by_cases hh6 : h ≤ 6 <;> omega
    · have hr3 : 3 ≤ r := by omega
      have hmul := Nat.mul_le_mul_left h hr3
      have hbase : 4*(h+r+1) ≤ (h+r+4)*(r+1) := by nlinarith
      exact hbase.trans (Nat.mul_le_mul_right (r+1) (by omega))
  have hratio : (4:ℝ)*((h:ℝ)+(r:ℝ)+1) ≤ ((j:ℝ)+1)*((r:ℝ)+1) := by
    exact_mod_cast hratioN
  have hp := mul_le_mul_of_nonneg_right hratio hx
  have hg := mul_le_mul_of_nonneg_left (show x ≤ 2*x-y by linarith)
    (show 0 ≤ ((j:ℝ)+1)*((r:ℝ)+1) by positivity)
  have ht : (4*Q)*((r:ℝ)+1) ≤ (((j:ℝ)+1)*(2*x-y))*((r:ℝ)+1) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ (show (0:ℝ) < (r:ℝ)+1 by positivity)).mp ht

def sourceWeight (B : ℕ → ℝ) (i : ℕ) : ℝ :=
  3*B (i+1)-B (i+2)-2*B i+(if i=0 then 1 else 0)
def dyadicPrefix (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), sourceWeight B i*((1:ℝ)/2)^(i+2)

theorem whole_generic_signed_dyadic_prefix_identity (B : ℕ → ℝ)
    (hB0 : B 0=1) (hB1 : B 1=1) (n : ℕ) :
    4*dyadicPrefix B n=1-4*(B (n+2)-B (n+1))*((1:ℝ)/2)^(n+2) := by
  induction n with
  | zero =>
    simp [dyadicPrefix,sourceWeight,hB0,hB1]
    ring_nf
  | succ n ih =>
    have hrec : dyadicPrefix B (n+1)=dyadicPrefix B n+
        sourceWeight B (n+1)*((1:ℝ)/2)^(n+3) := by
      simp [dyadicPrefix,Finset.sum_range_succ,Nat.add_assoc]
    have hw : sourceWeight B (n+1)=3*B (n+2)-B (n+3)-2*B (n+1) := by
      simp [sourceWeight,Nat.add_assoc]
    have hp : ((1:ℝ)/2)^(n+3)=((1:ℝ)/2)^(n+2)*(1/2) := by
      exact pow_succ _ _
    change 4*dyadicPrefix B (n+1)=1-4*(B (n+3)-B (n+2))*((1:ℝ)/2)^(n+3)
    rw [hrec,hw,hp]
    nlinarith

theorem whole_doubling_all_subreads (A : ℕ → ℝ)
    (hA : ∀ k, A (k+1) ≤ 2*A k) (n i : ℕ) (hi : i ≤ n) :
    A n ≤ (2:ℝ)^i*A (n-i) := by
  have whole : ∀ d u : ℕ, A (u+d) ≤ (2:ℝ)^d*A u := by
    intro d
    induction d with
    | zero => intro u; simp
    | succ d ih =>
      intro u
      have hstep := hA (u+d)
      have hprev := ih u
      have hm := mul_le_mul_of_nonneg_left hprev (show (0:ℝ) ≤ 2 by norm_num)
      simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm,Nat.add_assoc] using hstep.trans hm
  have heq : n-i+i=n := by omega
  simpa [heq] using whole i (n-i)

def payment (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), sourceWeight B i*A (n-i)

theorem whole_nonnegative_weighted_source_budget (A B : ℕ → ℝ) (n : ℕ)
    (hA : ∀ k, A (k+1) ≤ 2*A k)
    (hB0 : B 0=1) (hB1 : B 1=1)
    (hw : ∀ i ≤ n, 0 ≤ sourceWeight B i) :
    A n*((2:ℝ)^(n+2)-4*(B (n+2)-B (n+1))) ≤
      (2:ℝ)^(n+2)*payment A B n := by
  have hsum : 4*A n*dyadicPrefix B n ≤ payment A B n := by
    have hterm : ∀ i ∈ Finset.range (n+1),
        4*A n*(sourceWeight B i*((1:ℝ)/2)^(i+2)) ≤ sourceWeight B i*A (n-i) := by
      intro i hi
      have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
      have hd := whole_doubling_all_subreads A hA n i hin
      have hp0 : (0:ℝ) < 2^i := by positivity
      have hdiv : A n/(2:ℝ)^i ≤ A (n-i) := (div_le_iff₀ hp0).mpr (by nlinarith [hd])
      have hnorm : A n*((1:ℝ)/2)^i ≤ A (n-i) := by
        have heq : ((1:ℝ)/2)^i=((2:ℝ)^i)⁻¹ := by simp only [one_div,inv_pow]
        calc
          A n*((1:ℝ)/2)^i=A n/(2:ℝ)^i := by rw [heq,div_eq_mul_inv]
          _ ≤ A (n-i) := hdiv
      have hm := mul_le_mul_of_nonneg_left hnorm (hw i hin)
      have hp : ((1:ℝ)/2)^(i+2)=((1:ℝ)/2)^i*(1/4) := by
        rw [pow_add]
        norm_num
      rw [hp]
      nlinarith
    have hwhole := Finset.sum_le_sum hterm
    simpa [dyadicPrefix,payment,Finset.mul_sum] using hwhole
  have hid := whole_generic_signed_dyadic_prefix_identity B hB0 hB1 n
  have hform : A n*(1-4*(B (n+2)-B (n+1))*((1:ℝ)/2)^(n+2)) ≤ payment A B n := by
    rw [←hid]
    nlinarith [hsum]
  have hpow : (2:ℝ)^(n+2)*((1:ℝ)/2)^(n+2)=1 := by
    rw [←mul_pow]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hform
    (show (0:ℝ) ≤ (2:ℝ)^(n+2) by positivity)
  have heq : (2:ℝ)^(n+2)*(A n*(1-4*(B (n+2)-B (n+1))*((1:ℝ)/2)^(n+2)))=
      A n*((2:ℝ)^(n+2)-4*(B (n+2)-B (n+1))) := by
    calc
      _ = A n*((2:ℝ)^(n+2)-4*(B (n+2)-B (n+1))*
          ((2:ℝ)^(n+2)*((1:ℝ)/2)^(n+2))) := by ring
      _ = _ := by rw [hpow]; ring_nf
  rw [heq] at hscaled
  exact hscaled

theorem whole_indexed_gap_thin_slope_excludes_recovery (A B : ℕ → ℝ) (n : ℕ) (R : ℝ)
    (hA : ∀ k, A (k+1) ≤ 2*A k) (hAn : 0 ≤ A n)
    (hB0 : B 0=1) (hB1 : B 1=1)
    (hw : ∀ i ≤ n, 0 ≤ sourceWeight B i)
    (hD : 0 ≤ B (n+2)-B (n+1))
    (hgap : 4*A n ≤ ((n:ℝ)+2)*R)
    (hthin : ((n:ℝ)+2)*(B (n+2)-B (n+1)) ≤ (2:ℝ)^(n+2)) :
    A n-R-payment A B n ≤ 0 := by
  have hpay := whole_nonnegative_weighted_source_budget A B n hA hB0 hB1 hw
  have hR : 0 ≤ R := by nlinarith
  have hg := mul_le_mul_of_nonneg_right hgap hD
  have ht := mul_le_mul_of_nonneg_left hthin hR
  have hcomp : 4*A n*(B (n+2)-B (n+1)) ≤ R*(2:ℝ)^(n+2) := by nlinarith
  have hp0 : (0:ℝ) < 2^(n+2) := by positivity
  have hmult : (2:ℝ)^(n+2)*(A n-R) ≤ (2:ℝ)^(n+2)*payment A B n := by nlinarith
  have hfinal := (mul_le_mul_iff_right₀ hp0).mp hmult
  linarith

theorem whole_high_first_missing_degree_and_birth_guards (K : ℕ) (hK : 20 ≤ K) :
    18 ≤ K-2 ∧ 154 ≤ 1+(K-3)*(K-2)/2 ∧
    K-4 ≤ (1+(K-2)*(K-1)/2)/2 := by
  have hprod : 17*18 ≤ (K-3)*(K-2) := Nat.mul_le_mul (by omega) (by omega)
  have hquad : 4*(K-2) ≤ (K-2)*(K-1) := by
    have h := Nat.mul_le_mul_left (K-2) (show 4 ≤ K-1 by omega)
    simpa [Nat.mul_comm] using h
  omega

#print axioms whole_indexed_owner_raw_gap
#print axioms whole_generic_signed_dyadic_prefix_identity
#print axioms whole_doubling_all_subreads
#print axioms whole_nonnegative_weighted_source_budget
#print axioms whole_indexed_gap_thin_slope_excludes_recovery
#print axioms whole_high_first_missing_degree_and_birth_guards
end
end ActualDyadicSourcePayment
