import Mathlib

/- Unbounded kernel proofs of the signed-window tail and the subtraction splice.
   These formalize the new scalar-sequence step. They do not formalize the
   entire composition-ideal theorem or assert the unresolved product step. -/
set_option maxHeartbeats 0
namespace SignedWindowTail

def window (t : ℕ) (p : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ i ∈ Finset.range t, p (n - (i : ℤ))

def pos (x : ℝ) : ℝ := max x 0

theorem window_step (t : ℕ) (p : ℤ → ℝ) (n : ℤ) :
    window t p (n+1) - window t p n = p (n+1)-p (n+1-(t:ℤ)) := by
  induction t with
  | zero => simp [window]
  | succ t ih =>
    simp only [window, Finset.sum_range_succ] at *
    push_cast
    have he : n + 1 - ((t:ℤ)+1) = n-(t:ℤ) := by omega
    rw [he]
    linarith

theorem window_nonpos (t : ℕ) (p : ℤ → ℝ) (n R : ℤ)
    (hp : ∀ i, R < i → p i ≤ 0) (hn : R < n+1-(t:ℤ)) :
    window t p n ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply hp
  have hi' : i < t := Finset.mem_range.mp hi
  omega

theorem positive_window_tail (t : ℕ) (p : ℤ → ℝ) (n R : ℤ)
    (hleft : ∀ i, i ≤ R → 0 ≤ p i)
    (hright : ∀ i, R < i → p i ≤ 0) (hn : R ≤ n) :
    pos (window t p (n+1)) ≤ pos (window t p n) := by
  by_cases hc : n+1-(t:ℤ) ≤ R
  · have hu := hright (n+1) (by omega)
    have hl := hleft (n+1-(t:ℤ)) hc
    have hd := window_step t p n
    unfold pos
    exact max_le_max (by linarith) le_rfl
  · have hz : window t p (n+1) ≤ 0 :=
      window_nonpos t p (n+1) R hright (by omega)
    simp only [pos, max_eq_right hz]
    exact le_max_right _ _

theorem positive_window_after_support (t : ℕ) (p : ℤ → ℝ) (n R L : ℤ)
    (hleft : ∀ i, i ≤ R → 0 ≤ p i)
    (hright : ∀ i, R < i → p i ≤ 0)
    (hzero : ∀ i, L < i → p i = 0) (hn : L ≤ n) :
    pos (window t p (n+1)) ≤ pos (window t p n) := by
  by_cases hc : n+1-(t:ℤ) ≤ R
  · have hu := hzero (n+1) (by omega)
    have hl := hleft (n+1-(t:ℤ)) hc
    have hd := window_step t p n
    unfold pos
    exact max_le_max (by linarith) le_rfl
  · have hz : window t p (n+1) ≤ 0 :=
      window_nonpos t p (n+1) R hright (by omega)
    simp only [pos, max_eq_right hz]
    exact le_max_right _ _

theorem pos_sub_one (x : ℝ) : pos (x-1) = pos (pos x-1) := by
  unfold pos
  by_cases h : 0 ≤ x
  · rw [max_eq_left h]
  · have hx : x ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hx]
    have hsub : x-1 ≤ 0 := by linarith
    rw [max_eq_right hsub]
    norm_num

theorem subtraction_preserves_step (x y : ℝ) (h : pos y ≤ pos x) :
    pos (y-1) ≤ pos (x-1) := by
  rw [pos_sub_one y, pos_sub_one x]
  unfold pos at *
  exact max_le_max (by linarith) le_rfl

def subtractInterval (w : ℤ → ℝ) (A B n : ℤ) : ℝ :=
  w n - if A ≤ n ∧ n ≤ B then 1 else 0

theorem subtraction_tail (w : ℤ → ℝ) (L A B n : ℤ)
    (_hLA : L < A) (hAB : A ≤ B)
    (hdec : ∀ i, L ≤ i → pos (w (i+1)) ≤ pos (w i))
    (hzero : ∀ i, B ≤ i → w i = 0) (hn : L ≤ n) :
    pos (subtractInterval w A B (n+1)) ≤
      pos (subtractInterval w A B n) := by
  by_cases hna : n < A
  · by_cases hn1a : n+1 < A
    · simp only [subtractInterval, show ¬(A ≤ n+1 ∧ n+1 ≤ B) by omega,
        show ¬(A ≤ n ∧ n ≤ B) by omega, ite_false, sub_zero]
      exact hdec n hn
    · have he : n+1 = A := by omega
      simp only [subtractInterval, he,
        show A ≤ A ∧ A ≤ B from ⟨le_rfl,hAB⟩,
        show ¬(A ≤ n ∧ n ≤ B) by omega, ite_false, sub_zero]
      have hstep := hdec n hn
      rw [he] at hstep
      have hs : pos (w A-1) ≤ pos (w A) := by
        unfold pos
        exact max_le_max (by linarith) le_rfl
      exact le_trans hs hstep
  · by_cases hnb : n < B
    · simp only [subtractInterval,
        show A ≤ n+1 ∧ n+1 ≤ B by omega,
        show A ≤ n ∧ n ≤ B by omega]
      exact subtraction_preserves_step _ _ (hdec n hn)
    · have hz0 := hzero n (by omega)
      have hz1 := hzero (n+1) (by omega)
      simp only [subtractInterval, hz0, hz1,
        show ¬(A ≤ n+1 ∧ n+1 ≤ B) by omega, ite_false, sub_zero]
      unfold pos
      split_ifs <;> norm_num

def UnimodalNat (f : ℕ → ℝ) : Prop :=
  ∃ m, (∀ i j, i ≤ j → j ≤ m → f i ≤ f j) ∧
       (∀ i j, m ≤ i → i ≤ j → f j ≤ f i)

theorem tail_steps_antitone (f : ℕ → ℝ) (R : ℕ)
    (hstep : ∀ n, R ≤ n → f (n+1) ≤ f n)
    (i j : ℕ) (hi : R ≤ i) (hij : i ≤ j) : f j ≤ f i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact le_trans (hstep j (by omega)) ih

/-- A complete all-rank splice, used both for the raw one-part base
    and for the positive part of a signed uniform window. -/
theorem prefix_tail_unimodal (f v : ℕ → ℝ) (R : ℕ)
    (hv : UnimodalNat v) (hprefix : ∀ n, n ≤ R → f n=v n)
    (htail : ∀ n, R ≤ n → f (n+1) ≤ f n) : UnimodalNat f := by
  rcases hv with ⟨m,hinc,hdec⟩
  by_cases hm : m ≤ R
  · refine ⟨m,?_,?_⟩
    · intro i j hij hjm
      rw [hprefix i (by omega),hprefix j (by omega)]
      exact hinc i j hij hjm
    · intro i j hmi hij
      by_cases hjR : j ≤ R
      · rw [hprefix i (by omega),hprefix j hjR]
        exact hdec i j hmi hij
      · by_cases hiR : i ≤ R
        · have ht := tail_steps_antitone f R htail R j (by omega) (by omega)
          rw [hprefix R (by omega)] at ht
          rw [hprefix i hiR]
          exact le_trans ht (hdec i R hmi hiR)
        · exact tail_steps_antitone f R htail i j (by omega) hij
  · refine ⟨R,?_,?_⟩
    · intro i j hij hjR
      rw [hprefix i (by omega),hprefix j hjR]
      exact hinc i j hij (by omega)
    · intro i j hRi hij
      exact tail_steps_antitone f R htail i j hRi hij

/-- Uniform convolution of the nonnegative positive part supplies hv.
    The remaining signed comparison and all-rank join are kernel proved. -/
theorem positive_window_unimodal (t R : ℕ) (p : ℤ → ℝ)
    (hleft : ∀ i, i ≤ (R:ℤ) → 0 ≤ p i)
    (hright : ∀ i, (R:ℤ) < i → p i ≤ 0)
    (hv : UnimodalNat (fun n => window t (fun j => pos (p j)) (n:ℤ))) :
    UnimodalNat (fun n => pos (window t p (n:ℤ))) := by
  apply prefix_tail_unimodal _ _ R hv
  · intro n hn
    have he : window t p (n:ℤ) = window t (fun j => pos (p j)) (n:ℤ) := by
      unfold window
      apply Finset.sum_congr rfl
      intro i hi
      have hp := hleft ((n:ℤ)-(i:ℤ)) (by omega)
      exact (max_eq_left hp).symm
    rw [he]
    unfold pos
    apply max_eq_left
    apply Finset.sum_nonneg
    intro i hi
    exact le_max_right _ _
  · intro n hn
    have ht := positive_window_tail t p (n:ℤ) (R:ℤ) hleft hright (by omega)
    simpa only [Nat.cast_add,Nat.cast_one] using ht

theorem positive_support_initial (f : ℕ → ℝ) (hf : UnimodalNat f)
    (h0 : 0 < f 0) (i j : ℕ) (hij : i ≤ j) (hj : 0 < f j) : 0 < f i := by
  rcases hf with ⟨m,hinc,hdec⟩
  by_cases hi : i ≤ m
  · have he := hinc 0 i (by omega) hi
    linarith
  · have he := hdec i j (by omega) hij
    linarith

#print axioms window_step
#print axioms positive_window_tail
#print axioms positive_window_after_support
#print axioms subtraction_tail
#print axioms prefix_tail_unimodal
#print axioms positive_window_unimodal
#print axioms positive_support_initial
end SignedWindowTail
