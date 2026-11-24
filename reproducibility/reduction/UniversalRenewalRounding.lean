import Mathlib
set_option maxHeartbeats 2000000
namespace UniversalRenewalRounding

def read (U : ℕ → ℝ) (n i : ℕ) : ℝ := if i ≤ n then U (n-i) else 0

theorem entire_probability_renewal_unit_interval (t : ℕ) (a U : ℕ → ℝ)
    (ht : 2 ≤ t) (ha : ∀ i, i<t → 0<a i)
    (hmass : ∑ i ∈ Finset.range t, a i=1) (hzero : U 0=1)
    (hrec : ∀ n, U (n+1)=∑ i ∈ Finset.range t, a i*read U n i) :
    ∀ n, 0<U n ∧ U n ≤ 1 ∧ (0<n → U n<1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hzero]
    | succ n =>
      have hr : ∀ i, 0 ≤ read U n i ∧ read U n i ≤ 1 := by
        intro i
        by_cases hi : i ≤ n
        · have hprev := ih (n-i) (by omega)
          simp only [read, hi, ite_true]
          exact ⟨le_of_lt hprev.1,hprev.2.1⟩
        · simp [read,hi]
      have hle : ∀ i ∈ Finset.range t, a i*read U n i ≤ a i := by
        intro i hi
        have hai := le_of_lt (ha i (Finset.mem_range.mp hi))
        nlinarith [(hr i).2]
      have hex : ∃ i ∈ Finset.range t, a i*read U n i<a i := by
        by_cases hn : n=0
        · refine ⟨1,by simp; omega,?_⟩
          have hai := ha 1 (by omega)
          simp [hn,read,hai]
        · refine ⟨0,by simp; omega,?_⟩
          have hai := ha 0 (by omega)
          have hui := (ih n (by omega)).2.2 (by omega)
          simp only [read, Nat.zero_le, ite_true, Nat.sub_zero]
          nlinarith
      have hstrict : U (n+1)<1 := by
        rw [hrec n]
        have hh := Finset.sum_lt_sum hle hex
        simpa only [hmass] using hh
      have hpositive : 0<U (n+1) := by
        have hai := ha 0 (by omega)
        have hui := (ih n (by omega)).1
        have hterm : a 0*read U n 0 ≤ ∑ i ∈ Finset.range t,a i*read U n i := by
          exact Finset.single_le_sum (f:=fun i => a i*read U n i)
            (s:=Finset.range t)
            (fun i hi => mul_nonneg (le_of_lt (ha i (Finset.mem_range.mp hi))) (hr i).1)
            (Finset.mem_range.mpr (show 0<t by omega))
        simp only [read, Nat.zero_le, ite_true, Nat.sub_zero] at hterm
        rw [hrec n]
        exact lt_of_lt_of_le (mul_pos hai hui) hterm
      exact ⟨hpositive,le_of_lt hstrict,fun _ => hstrict⟩

theorem entire_renewal_signed_increment_strict_bound (U : ℕ → ℝ)
    (h : ∀ n,0<U n ∧ U n ≤ 1 ∧ (0<n → U n<1)) :
    ∀ n, -1<U (n+1)-U n ∧ U (n+1)-U n<1 := by
  intro n
  have hprev := h n
  have hnext := h (n+1)
  have hstrict := hnext.2.2 (by omega)
  constructor <;> linarith

theorem whole_mixture_normalizer_identity (R : Type*) [CommRing R]
    (t : ℕ) (a : ℕ → R) (hmass : ∑ i ∈ Finset.range t,a i=1) :
    let B : Polynomial R := ∑ i ∈ Finset.range t,
      Polynomial.C (a i)*(∑ j ∈ Finset.range (i+1), Polynomial.X^j)
    (1-Polynomial.X)*B=1-∑ i ∈ Finset.range t,
      Polynomial.C (a i)*Polynomial.X^(i+1) := by
  dsimp
  have hgeo : ∀ n : ℕ,(1-(Polynomial.X : Polynomial R))*
      (∑ j ∈ Finset.range n,Polynomial.X^j)=1-Polynomial.X^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ,mul_add,ih,pow_succ]
        ring
  calc
    _ = ∑ i ∈ Finset.range t,Polynomial.C (a i)*
        ((1-Polynomial.X)*(∑ j ∈ Finset.range (i+1),Polynomial.X^j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i ∈ Finset.range t,Polynomial.C (a i)*(1-Polynomial.X^(i+1)) := by
          simp_rw [hgeo]
    _ = _ := by
          simp_rw [mul_sub,mul_one]
          rw [Finset.sum_sub_distrib]
          have hc : (∑ i ∈ Finset.range t,Polynomial.C (a i))=1 := by
            rw [← map_sum,hmass]
            simp
          rw [hc]

#print axioms entire_probability_renewal_unit_interval
#print axioms entire_renewal_signed_increment_strict_bound
#print axioms whole_mixture_normalizer_identity
end UniversalRenewalRounding
