import RegularizedFibonacciEnvelope

set_option maxHeartbeats 0
namespace BinaryRelativeFibonacci
open RegularizedFibonacciEnvelope

def minor (d : ℕ → ℤ) (n : ℕ) : ℤ := d n ^ 2-d (n-1)*d (n+1)

theorem two_term_cross (A B C D : ℤ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 < B) (h1 : 0 ≤ B^2-A*C) (h2 : 0 ≤ C^2-B*D) :
    0 ≤ B*C-A*D := by
  have hp := mul_nonneg hC h1
  have hq := mul_nonneg hA h2
  have hs : 0 ≤ B*(B*C-A*D) := by nlinarith only [hp,hq]
  exact (mul_nonneg_iff_of_pos_left hB).mp hs

theorem strict_two_term_window (A B C D : ℤ)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (h1 : 0 ≤ B^2-A*C) (h2 : 0 ≤ C^2-B*D)
    (hstrict : C ≠ 0 → 1 ≤ C^2-B*D) (hzero : C=0 → D=0) :
    1 ≤ (B+C)^2-(A+B)*(C+D) := by
  have hc := two_term_cross A B C D hA hC (by omega) h1 h2
  by_cases hz : C=0
  · have hd := hzero hz
    rw [hz,hd]
    nlinarith
  · have hs := hstrict hz
    nlinarith

theorem Fibonacci_first_defect_boundary (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ fi (h+1)^2-fi h*(fi (h+2)-1) := by
  have hc := cassini h
  have hp := positive_fibonacci h hh
  have hs := sign_power_bounds h
  nlinarith [hs.1]

theorem integer_strict_minor_relative_transfer (A B C r s t : ℤ)
    (hp : 0 ≤ A*C) (hu : A*C ≤ r*t) (hr : 0 ≤ r*t)
    (hminor : 1 ≤ B^2-A*C) (hCassini : s^2-r*t ≤ 1) :
    A*C*s^2 ≤ B^2*r*t := by
  have h1 := mul_nonneg hr (sub_nonneg.mpr hminor)
  have h2 := mul_nonneg hp (sub_nonneg.mpr hCassini)
  nlinarith only [h1,h2,hu]

theorem support_nonnegative (d : ℕ → ℤ) (L : ℕ)
    (hp : ∀ n, n ≤ L → 1 ≤ d n) (hz : ∀ n, L < n → d n=0) :
    ∀ n, 0 ≤ d n := by
  intro n
  by_cases hn : n ≤ L
  · have hh := hp n hn; omega
  · rw [hz n (by omega)]

-- This is a genuine unbounded induction.  The hypotheses describe arbitrary
-- terminal-trim histories; the exact word-to-history identification is written.
theorem arbitrary_trim_tail_induction (d : ℕ → ℕ → ℤ) (L : ℕ → ℕ)
    (hp : ∀ h n, 2 ≤ h → n ≤ L h → 1 ≤ d h n)
    (hz : ∀ h n, 2 ≤ h → L h < n → d h n=0)
    (hpre : ∀ h n, 2 ≤ h → n < h → d h n=fi (n+1))
    (hdef : ∀ h, 2 ≤ h → d h h ≤ fi (h+1)-1)
    (hL : ∀ h, 2 ≤ h → L (h+1) ≤ L h+2)
    (heq : ∀ h n, 2 ≤ h → 1 ≤ n → n ≤ L h+1 →
      d (h+1) n=d h (n-1)+(if 2 ≤ n then d h (n-2) else 0))
    (hle : ∀ h n, 2 ≤ h → 2 ≤ n →
      d (h+1) n ≤ d h (n-1)+d h (n-2))
    (hbase : ∀ n, 1 ≤ n → 0 ≤ minor (d 2) n ∧
      (2 ≤ n → 0 < d 2 n → 1 ≤ minor (d 2) n)) :
    ∀ h, 2 ≤ h → ∀ n, h-1 ≤ n → 0 ≤ minor (d h) n ∧
      (h ≤ n → 0 < d h n → 1 ≤ minor (d h) n) := by
  intro h hh
  induction h, hh using Nat.le_induction with
  | base => simpa using hbase
  | succ h hh ih =>
    intro n hn
    have hnew : 2 ≤ h+1 := by omega
    have hnon := support_nonnegative (d h) (L h)
      (fun i hi => hp h i hh hi) (fun i hi => hz h i hh hi)
    by_cases hout : L (h+1) < n
    · have h0 := hz (h+1) n hnew hout
      have h1 := hz (h+1) (n+1) hnew (by omega)
      simp [minor,h0,h1]
    by_cases hlast : n=L (h+1)
    · have h0 := hz (h+1) (n+1) hnew (by omega)
      have h1 := hp (h+1) n hnew (by omega)
      simp only [minor,h0,mul_zero,sub_zero]
      constructor
      · positivity
      · intro _ _; nlinarith
    by_cases hboundary : n=h
    · subst n
      have hp0 := hpre (h+1) (h-1) hnew (by omega)
      have hp1 := hpre (h+1) h hnew (by omega)
      have hd := hdef (h+1) hnew
      have he : h-1+1=h := by omega
      rw [he] at hp0
      have hf := positive_fibonacci h (by omega)
      have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ fi h by omega)
      have hb := Fibonacci_first_defect_boundary h (by omega)
      constructor
      · dsimp [minor]; rw [hp0,hp1]; nlinarith only [hm,hb]
      · intro hi; omega
    have hn3 : 3 ≤ n := by omega
    have hnc : n ≤ L h+1 := by have hl := hL h hh; omega
    have hb := hp h (n-2) hh (by omega)
    have hi1 := ih (n-2) (by omega)
    have hi2 := ih (n-1) (by omega)
    have he1 : n-2-1=n-3 := by omega
    have he2 : n-2+1=n-1 := by omega
    have he3 : n-1-1=n-2 := by omega
    have he4 : n-1+1=n := by omega
    dsimp [minor] at hi1 hi2
    rw [he1,he2] at hi1
    rw [he3,he4] at hi2
    have hzero : d h (n-1)=0 → d h n=0 := by
      intro hc
      by_cases hci : n-1 ≤ L h
      · have hcp := hp h (n-1) hh hci; omega
      · exact hz h n hh (by omega)
    have hs := strict_two_term_window (d h (n-3)) (d h (n-2))
      (d h (n-1)) (d h n) (hnon _) hb (hnon _) hi1.1 hi2.1
      (fun hc => hi2.2 (by omega) (by have hcn := hnon (n-1); omega)) hzero
    have heprev := heq h (n-1) hh (by omega) (by omega)
    have hecur := heq h n hh (by omega) hnc
    simp only [show 2 ≤ n-1 by omega, show 2 ≤ n by omega, ite_true,
      he3] at heprev hecur
    have heprev2 : n-1-2=n-3 := by omega
    rw [heprev2] at heprev
    have hnext := hle h (n+1) hh (by omega)
    have hne1 : n+1-1=n := by omega
    have hne2 : n+1-2=n-1 := by omega
    rw [hne1,hne2] at hnext
    have hm := mul_le_mul_of_nonneg_left hnext
      (show 0 ≤ d h (n-2)+d h (n-3) by have ha := hnon (n-3); omega)
    have hres : 1 ≤ minor (d (h+1)) n := by
      dsimp [minor]
      rw [heprev,hecur]
      nlinarith only [hs,hm]
    exact ⟨by omega, fun _ _ => hres⟩

theorem relative_LC_from_tail (d : ℕ → ℤ) (L h : ℕ) (_hh : 2 ≤ h)
    (hp : ∀ n, n ≤ L → 1 ≤ d n) (hz : ∀ n, L < n → d n=0)
    (hpre : ∀ n, n < h → d n=fi (n+1))
    (hbound : ∀ n, d n ≤ fi (n+1))
    (hstrict : ∀ n, h ≤ n → 0 < d n → 1 ≤ minor d n) :
    ∀ n, 1 ≤ n → d (n-1)*d (n+1)*fi (n+1)^2 ≤
      d n^2*fi n*fi (n+2) := by
  have hnon := support_nonnegative d L hp hz
  intro n hn
  have hf : 0 ≤ fi n := by have hhf := positive_fibonacci n hn; omega
  have hn1 : n-1+1=n := by omega
  have hn2 : n+1+1=n+2 := by omega
  by_cases hearly : n < h
  · have he0 := hpre (n-1) (by omega)
    have he1 := hpre n hearly
    rw [hn1] at he0
    rw [he0,he1]
    have hb := hbound (n+1)
    rw [hn2] at hb
    have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hf (sq_nonneg (fi (n+1))))
    nlinarith only [hm]
  by_cases hzero : d n=0
  · have hnout : L < n := by
      by_contra h
      have hpos := hp n (by omega)
      omega
    have hnz := hz (n+1) (by omega)
    simp [hzero,hnz]
  have hpos : 0 < d n := by have hp0 := hnon n; omega
  have hs := hstrict n (by omega) hpos
  have hc := cassini n
  have hsgn := sign_power_bounds n
  have hbp := hbound (n-1)
  have hbn := hbound (n+1)
  rw [hn1] at hbp
  rw [hn2] at hbn
  have hu : d (n-1)*d (n+1) ≤ fi n*fi (n+2) :=
    mul_le_mul hbp hbn (hnon _) hf
  have ht := integer_strict_minor_relative_transfer (d (n-1)) (d n)
    (d (n+1)) (fi n) (fi (n+1)) (fi (n+2))
    (mul_nonneg (hnon _) (hnon _)) hu
    (by have hp2 := positive_fibonacci (n+2) (by omega); positivity)
    hs (by omega)
  nlinarith only [ht]

#print axioms two_term_cross
#print axioms strict_two_term_window
#print axioms Fibonacci_first_defect_boundary
#print axioms integer_strict_minor_relative_transfer
#print axioms support_nonnegative
#print axioms arbitrary_trim_tail_induction
#print axioms relative_LC_from_tail
end BinaryRelativeFibonacci
