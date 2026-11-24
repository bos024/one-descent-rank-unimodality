import Mathlib

set_option maxHeartbeats 0
open scoped goldenRatio
namespace ArbitraryFibonacciTailLateC

private theorem phi_lower : (8/5:ℝ) < φ := by
  nlinarith [Real.goldenRatio_sq,Real.one_lt_goldenRatio]

private theorem phi_upper : φ < (13/8:ℝ) := by
  nlinarith [Real.goldenRatio_sq,Real.one_lt_goldenRatio]

noncomputable def baseG (k : ℕ) : ℝ := (Nat.fib (k+3):ℝ)-1

theorem complete_regularized_Fibonacci_uniform_margin (k : ℕ) :
    (1/3:ℝ) ≤ baseG (k+1)-φ*baseG k := by
  have hneg := Real.goldenConj_neg
  have habs : |ψ| ≤ (5/8:ℝ) := by
    rw [abs_of_neg hneg]
    linarith [Real.goldenRatio_add_goldenConj,phi_upper]
  have hpow : |ψ^(k+3)| ≤ (5/8:ℝ)^3 := by
    rw [abs_pow]
    calc
      |ψ|^(k+3) ≤ |ψ|^3 :=
        pow_le_pow_of_le_one (abs_nonneg ψ) (by linarith only [habs]) (by omega)
      _ ≤ (5/8:ℝ)^3 := by gcongr
  have hid := Real.fib_succ_sub_goldenRatio_mul_fib (k+3)
  have hident : baseG (k+1)-φ*baseG k=φ-1+ψ^(k+3) := by
    unfold baseG
    simpa only [Nat.add_assoc] using (show
      (Nat.fib (k+3+1):ℝ)-1-φ*((Nat.fib (k+3):ℝ)-1)=φ-1+ψ^(k+3) by
      nlinarith only [hid])
  rw [hident]
  have hl := (abs_le.mp hpow).1
  nlinarith only [hl,phi_lower]

theorem complete_positive_numerator_margin_transport
    (s : Finset ℕ) (B : ℕ → ℝ) (g : ℤ → ℝ) (k : ℤ)
    (hzero : 0 ∈ s) (hB0 : B 0=1)
    (hB : ∀ i ∈ s, 0 ≤ B i)
    (hg : ∀ i ∈ s, 0 ≤ g (k-(i:ℤ))-φ*g (k-1-(i:ℤ)))
    (hbase : (1/3:ℝ) ≤ g k-φ*g (k-1)) :
    (1/3:ℝ) ≤ (∑ i ∈ s, B i*g (k-(i:ℤ)))-
      φ*(∑ i ∈ s, B i*g (k-1-(i:ℤ))) := by
  have hs := Finset.single_le_sum (s:=s)
    (f:=fun i => B i*(g (k-(i:ℤ))-φ*g (k-1-(i:ℤ))))
    (fun i hi => mul_nonneg (hB i hi) (hg i hi)) hzero
  simp only [Nat.cast_zero,sub_zero,hB0,one_mul] at hs
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hs
  have he : (∑ i ∈ s, B i*(φ*g (k-1-(i:ℤ)))) =
      φ*(∑ i ∈ s, B i*g (k-1-(i:ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [he] at hs
  exact le_trans hbase hs

noncomputable def rootWindow (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (-φ)^(j+1)

private theorem rootWindow_identity (t : ℕ) : φ*rootWindow t=(-φ)^t-1 := by
  induction t with
  | zero => simp [rootWindow]
  | succ t ih =>
    have hs : rootWindow (t+1)=rootWindow t+(-φ)^(t+1) :=
      Finset.sum_range_succ _ _
    have hm := congrArg (fun x : ℝ => x*((-φ)^t)) Real.goldenRatio_sq
    rw [hs,pow_succ]
    nlinarith only [ih,hm]

theorem complete_capacity_window_conjugate_norm (t : ℕ) (ht : 2 ≤ t) :
    |rootWindow t| ≤ φ^t := by
  have hphi := Real.goldenRatio_pos
  have hident := congrArg abs (rootWindow_identity t)
  simp only [abs_mul,abs_of_pos hphi] at hident
  have htri : |(-φ)^t-1| ≤ φ^t+1 := by
    calc
      |(-φ)^t-1| = |(-φ)^t+(-1)| := rfl
      _ ≤ |(-φ)^t|+|(-1:ℝ)| := abs_add_le _ _
      _ = φ^t+1 := by simp [abs_pow,abs_of_pos hphi]
  have hp : φ ≤ φ^t := by
    calc
      φ=φ^1 := by simp
      _ ≤ φ^t := pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) (by omega)
  have hrel := mul_nonneg (show 0 ≤ φ-1 by linarith [Real.one_lt_goldenRatio])
    (show 0 ≤ φ^t-φ by linarith only [hp])
  have hh : φ*|rootWindow t| ≤ φ*(φ^t) := by
    nlinarith only [hident,htri,hrel,Real.goldenRatio_sq]
  exact (mul_le_mul_iff_right₀ hphi).mp hh

noncomputable def evalWord : List ℕ → ℝ
  | [] => 1
  | t::word => rootWindow t*evalWord word

theorem complete_arbitrary_word_conjugate_norm (word : List ℕ)
    (hword : ∀ t ∈ word, 2 ≤ t) : |evalWord word| ≤ φ^word.sum := by
  induction word with
  | nil => simp [evalWord]
  | cons t word ih =>
    have ht := complete_capacity_window_conjugate_norm t (hword t (by simp))
    have hp := ih (by intro x hx; exact hword x (by simp [hx]))
    have hh := mul_le_mul ht hp (abs_nonneg _) (show 0 ≤ φ^t by positivity)
    simpa [evalWord,abs_mul,List.sum_cons,pow_add] using hh

private theorem conjugate_power_reversal (n i : ℕ) (hi : i ≤ n) :
    ψ^(n-i)*φ^n=(-1:ℝ)^n*(-φ)^i := by
  have hephi : φ^n=φ^(n-i)*φ^i := by
    calc
      φ^n=φ^((n-i)+i) := by congr 1; omega
      _ = φ^(n-i)*φ^i := pow_add _ _ _
  have hesign : (-1:ℝ)^n=(-1:ℝ)^(n-i)*(-1:ℝ)^i := by
    calc
      (-1:ℝ)^n=(-1:ℝ)^((n-i)+i) := by congr 1; omega
      _ = (-1:ℝ)^(n-i)*(-1:ℝ)^i := pow_add _ _ _
  have hs : (-1:ℝ)^i*(-φ)^i=φ^i := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    ψ^(n-i)*φ^n=(ψ*φ)^(n-i)*φ^i := by rw [hephi,mul_pow]; ring
    _ = (-1:ℝ)^(n-i)*φ^i := by rw [Real.goldenConj_mul_goldenRatio]
    _ = (-1:ℝ)^n*(-φ)^i := by rw [hesign,mul_assoc,hs]

noncomputable def polyEval (B : ℕ → ℝ) (W : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (W+1), B i*x^i

noncomputable def tailError (B : ℕ → ℝ) (W n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (W+1), B i*ψ^(n-i)

theorem complete_scaled_finite_tail_error (B : ℕ → ℝ) (W n : ℕ)
    (hn : W ≤ n) (hbound : |polyEval B W (-φ)| ≤ φ^W) :
    |tailError B W n| *φ^n ≤ φ^W := by
  have hid : tailError B W n*φ^n=(-1:ℝ)^n*polyEval B W (-φ) := by
    unfold tailError polyEval
    rw [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hh := conjugate_power_reversal n i (by omega)
    calc
      B i*ψ^(n-i)*φ^n=B i*(ψ^(n-i)*φ^n) := by ring
      _ = (-1:ℝ)^n*(B i*(-φ)^i) := by rw [hh]; ring
  have habs := congrArg abs hid
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_pos Real.goldenRatio_pos] at habs
  exact le_trans (le_of_eq habs) hbound

theorem complete_late_error_one_sixth (W n : ℕ) (epsilon : ℝ)
    (hn : W+4 ≤ n) (hbound : |epsilon| *φ^n ≤ φ^W) : |epsilon| < 1/6 := by
  have hphi := Real.goldenRatio_pos
  have hp : φ^(W+4) ≤ φ^n :=
    pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) hn
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg epsilon)
  have he : |epsilon| *φ^4*φ^W ≤ 1*φ^W := by
    rw [pow_add] at hh
    nlinarith only [hh,hbound]
  have hc := (mul_le_mul_iff_left₀ (show 0 < φ^W by positivity)).mp he
  have hfour : φ^4=3*φ+2 := by
    calc
      φ^4=(φ^2)^2 := by ring
      _ = (φ+1)^2 := by rw [Real.goldenRatio_sq]
      _ = 3*φ+2 := by nlinarith only [Real.goldenRatio_sq]
  have hbig : (6:ℝ) < φ^4 := by rw [hfour]; linarith [phi_lower]
  by_contra hfail
  have hlow : (1/6:ℝ) ≤ |epsilon| := by linarith only [hfail]
  have hmul := mul_le_mul_of_nonneg_right hlow (show 0 ≤ φ^4 by positivity)
  nlinarith only [hmul,hc,hbig]

theorem strict_all_shift_C_payment (Gcur Gprev Dcur Dprev margin epsilon : ℝ)
    (hG : 0 ≤ Gprev) (hD : 0 < Dprev) (hread : Gprev ≤ 2*Dprev)
    (hmargin : (1/3:ℝ) ≤ margin) (herror : epsilon < 1/6)
    (hGid : Gcur=φ*Gprev+margin) (hDid : Dcur=φ*Dprev+epsilon) :
    0 < Gcur*Dprev-Gprev*Dcur := by
  have hm := mul_le_mul_of_nonneg_left hmargin (le_of_lt hD)
  rw [hGid,hDid]
  by_cases he : epsilon ≤ 0
  · have hp := mul_nonpos_of_nonneg_of_nonpos hG he
    nlinarith only [hm,hp,hD]
  · have hp := mul_le_mul_of_nonneg_right hread (show 0 ≤ epsilon by linarith only [he])
    have hs := mul_pos hD (show 0 < (1/3:ℝ)-2*epsilon by linarith only [herror])
    nlinarith only [hm,hp,hs]

#print axioms complete_regularized_Fibonacci_uniform_margin
#print axioms complete_positive_numerator_margin_transport
#print axioms complete_capacity_window_conjugate_norm
#print axioms complete_arbitrary_word_conjugate_norm
#print axioms complete_scaled_finite_tail_error
#print axioms complete_late_error_one_sixth
#print axioms strict_all_shift_C_payment
end ArbitraryFibonacciTailLateC
