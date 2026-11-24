import Mathlib
set_option maxHeartbeats 2500000
namespace MixedBinaryAllCounts

theorem all_finite_binary_seed_three_startup_budgets
    (w r a b c d : ℝ) (hw : 11 ≤ w) (_hr : 0 ≤ r) (hrw : r ≤ w)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (hc : 5 ≤ c) (hd : 11 ≤ d) :
    let B := w*a+b
    let C := w*(w+1)/2*a+w*b+c
    let D := (w*(w+1)*(w+2)/6-r)*a+w*(w+1)/2*b+w*c+d
    0 ≤ B-4*a-1 ∧ 0 ≤ C-4*B-1 ∧ 0 ≤ D-4*C-1 := by
  dsimp
  have a0 : 0 ≤ a := by linarith
  have b0 : 0 ≤ b := by linarith
  have c0 : 0 ≤ c := by linarith
  have d0 : 0 ≤ d-1 := by linarith
  have hA := mul_nonneg (show 0 ≤ w-4 by linarith) a0
  have hB := mul_nonneg (show 0 ≤ w-4 by linarith) b0
  have hC := mul_nonneg (show 0 ≤ w-4 by linarith) c0
  have hw0 : 0 ≤ w := by linarith
  have hw7 : 0 ≤ w-7 := by linarith
  have hk : 0 ≤ w*(w-7)/2 := by positivity
  have hka := mul_nonneg hk a0
  have hkb := mul_nonneg hk b0
  have hpoly : 0 ≤ w*(w+1)*(w-10)/6-w := by
    let x := w-11
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have he : w=11+x := by dsimp [x]; ring
    rw [he]; ring_nf; positivity
  have hk2 : 0 ≤ w*(w+1)*(w-10)/6-r := by linarith
  have hprod := mul_nonneg hk2 a0
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hA,hb]
  · nlinarith only [hka,hB,hc]
  · nlinarith only [hprod,hkb,hC,d0]

theorem complete_analytic_first_four_crossing (r u : ℕ) (hu : 2*r < u) :
    let s0 := (u-2*r)/3+1
    1 ≤ s0 ∧ u < 2*r+3*s0 ∧ 2*r+3*s0 ≤ u+3 ∧
    u+r+s0+2 ≥ 3*r+4*s0-1 ∧
    (∀ s, s < s0 → 2*r+3*s ≤ u) ∧
    (∀ s, u < 2*r+3*s → s0 ≤ s) := by
  dsimp
  have hm := Nat.mod_lt (u-2*r) (by norm_num : 0 < 3)
  have he := Nat.mod_add_div (u-2*r) 3
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro s hs; omega
  · intro s hs; omega

theorem complete_all_binary_and_four_count_induction
    (r u : ℕ) (P C : ℕ → Prop)
    (hbase : u ≤ 2*r → P 0)
    (hseed : 2*r < u → P ((u-2*r)/3+1))
    (hstep : ∀ s, P s → P (s+1))
    (hpaid : ∀ s, P s → C s)
    (hdense : ∀ s, 2*r+3*s ≤ u → C s) : ∀ s, C s := by
  intro s
  by_cases hu : u ≤ 2*r
  · apply hpaid s
    induction s with
    | zero => exact hbase hu
    | succ s ih => exact hstep s ih
  · have hu0 : 2*r < u := by omega
    by_cases hs : 2*r+3*s ≤ u
    · exact hdense s hs
    · have hstart : (u-2*r)/3+1 ≤ s :=
        (complete_analytic_first_four_crossing r u hu0).2.2.2.2.2 s (by omega)
      apply hpaid s
      exact Nat.le_induction (hseed hu0) (fun n _ h => hstep n h) s hstart

theorem exact_cassini_counter_triple_is_protected (r s u : ℕ)
    (hu : 2*r+3*s < u) :
    3*r+4*s+2 < u+r+s+2 := by omega

end MixedBinaryAllCounts
#print axioms MixedBinaryAllCounts.all_finite_binary_seed_three_startup_budgets
#print axioms MixedBinaryAllCounts.complete_analytic_first_four_crossing
#print axioms MixedBinaryAllCounts.complete_all_binary_and_four_count_induction
#print axioms MixedBinaryAllCounts.exact_cassini_counter_triple_is_protected
