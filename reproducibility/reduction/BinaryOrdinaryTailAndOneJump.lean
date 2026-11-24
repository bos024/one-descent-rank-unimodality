import Mathlib

set_option maxHeartbeats 0
namespace BinaryOrdinaryTailAndOneJump

def fi (n : ℕ) : ℤ := Nat.fib n
def minor (a : ℕ → ℤ) (n : ℕ) : ℤ := a n^2-a (n-1)*a (n+1)

-- Reproved local foundations, not counted again as new reports.
private theorem fi_rec (n : ℕ) : fi (n+2)=fi n+fi (n+1) := by
  unfold fi
  exact_mod_cast (Nat.fib_add_two (n:=n))

private theorem cassini (n : ℕ) : fi (n+1)^2-fi n*fi (n+2)=(-1:ℤ)^n := by
  induction n with
  | zero => norm_num [fi]
  | succ n ih =>
    change fi (n+2)^2-fi (n+1)*fi (n+3)=(-1:ℤ)^(n+1)
    have he : fi (n+2)^2-fi (n+1)*fi (n+3)=
        -(fi (n+1)^2-fi n*fi (n+2)) := by
      rw [fi_rec (n+1),fi_rec n];ring
    rw [he,ih,pow_succ];ring

private theorem sign_bounds (n : ℕ) : -1 ≤ (-1:ℤ)^n ∧ (-1:ℤ)^n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ];constructor <;> nlinarith [ih.1,ih.2]

theorem strict_binary_ordinary_boundary (h : ℕ) :
    1 ≤ fi (h+3)^2-fi (h+2)*(fi (h+4)-1) := by
  have hc := cassini (h+2)
  have hs := sign_bounds (h+2)
  cases h with
  | zero => norm_num [fi]
  | succ h =>
    have hn : 3 ≤ h+1+2 := by omega
    have hb : 2 ≤ fi (h+1+2) := by
      have hm := Nat.fib_mono hn
      norm_num at hm
      unfold fi
      exact_mod_cast hm
    nlinarith [hs.1]

theorem window_LC_strict_when_growing (A B C D : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h1 : 0 ≤ B^2-A*C) (h2 : 0 ≤ C^2-B*D)
    (hzB : B=0 → C=0) (hzC : C=0 → D=0)
    (hs1 : A<B → 1 ≤ B^2-A*C) (hs2 : B<C → 1 ≤ C^2-B*D) :
    0 ≤ (B+C)^2-(A+B)*(C+D) ∧
      (A+B<B+C → 1 ≤ (B+C)^2-(A+B)*(C+D)) := by
  by_cases hb0 : B=0
  · have hc0 := hzB hb0
    have hd0 := hzC hc0
    rw [hb0,hc0,hd0]
    constructor
    · norm_num
    · intro h;omega
  have hb : 0 < B := by omega
  have hp := mul_nonneg hC h1
  have hq := mul_nonneg hA h2
  have hc : 0 ≤ B*C-A*D := by
    have hh : 0 ≤ B*(B*C-A*D) := by nlinarith only [hp,hq]
    exact (mul_nonneg_iff_of_pos_left hb).mp hh
  constructor
  · nlinarith only [h1,h2,hc]
  · intro hg
    by_cases hAB : A<B
    · have hs := hs1 hAB;nlinarith only [hs,h2,hc]
    · have hBC : B<C := by omega
      have hs := hs2 hBC;nlinarith only [h1,hs,hc]

-- Whole unbounded induction on the number of twos.  The actual polynomial
-- recurrence, support, exact prefix and rectangular base are written inputs.
theorem ordinary_binary_full_tail_induction (F : ℕ → ℕ → ℤ)
    (hp : ∀ h n, 0 ≤ F h n)
    (hz : ∀ h n, F h n=0 → F h (n+1)=0)
    (hpre : ∀ h n, n ≤ h+1 → F h n=fi (n+1))
    (hdef : ∀ h, F h (h+2) ≤ fi (h+3)-1)
    (hrec : ∀ h n, 2 ≤ n → F (h+1) n=F h (n-1)+F h (n-2))
    (hbase : ∀ n, 1 ≤ n → 0 ≤ minor (F 0) n ∧
      (F 0 (n-1)<F 0 n → 1 ≤ minor (F 0) n)) :
    ∀ h n, h+1 ≤ n → 0 ≤ minor (F h) n ∧
      (F h (n-1)<F h n → 1 ≤ minor (F h) n) := by
  intro h
  induction h with
  | zero => simpa using hbase
  | succ h ih =>
    intro n hn
    by_cases hb : n=h+2
    · subst n
      have he0 := hpre (h+1) (h+1) (by omega)
      have he1 := hpre (h+1) (h+2) (by omega)
      have he2 := hdef (h+1)
      have hidx : h+1+2=h+3 := by omega
      have hidx2 : h+1+3=h+4 := by omega
      rw [hidx,hidx2] at he2
      have hm := mul_le_mul_of_nonneg_left he2
        (show 0 ≤ fi (h+2) by unfold fi;positivity)
      have hs := strict_binary_ordinary_boundary h
      have hres : 1 ≤ minor (F (h+1)) (h+2) := by
        dsimp [minor]
        rw [he0,he1]
        nlinarith only [hm,hs]
      exact ⟨by omega,fun _ => hres⟩
    have hn3 : 3 ≤ n := by omega
    have hi1 := ih (n-2) (by omega)
    have hi2 := ih (n-1) (by omega)
    have he1 : n-2-1=n-3 := by omega
    have he2 : n-2+1=n-1 := by omega
    have he3 : n-1-1=n-2 := by omega
    have he4 : n-1+1=n := by omega
    dsimp [minor] at hi1 hi2
    rw [he1,he2] at hi1
    rw [he3,he4] at hi2
    have hs := window_LC_strict_when_growing
      (F h (n-3)) (F h (n-2)) (F h (n-1)) (F h n)
      (hp _ _) (hp _ _) (hp _ _) hi1.1 hi2.1
      (fun hh => by simpa only [he2] using hz h (n-2) hh)
      (fun hh => by simpa only [he4] using hz h (n-1) hh)
      hi1.2 hi2.2
    have hpv := hrec h (n-1) (by omega)
    have hcv := hrec h n (by omega)
    have hnv := hrec h (n+1) (by omega)
    have he5 : n-1-2=n-3 := by omega
    have he6 : n+1-1=n := by omega
    have he7 : n+1-2=n-1 := by omega
    rw [he3,he5] at hpv
    rw [he6,he7] at hnv
    dsimp [minor]
    rw [hpv,hcv,hnv]
    constructor
    · nlinarith only [hs.1]
    · intro hg
      have hsg := hs.2 (by omega)
      nlinarith only [hsg]

theorem ordinary_binary_relative_LC_prefix (F : ℕ → ℤ) (h R : ℕ)
    (hp : ∀ n, 0 ≤ F n) (hb : ∀ n, F n ≤ fi (n+1))
    (hpre : ∀ n, n ≤ h+1 → F n=fi (n+1))
    (hg : ∀ n, 2 ≤ n → n ≤ R → F (n-1)<F n)
    (hs : ∀ n, h+1 ≤ n → F (n-1)<F n → 1 ≤ minor F n) :
    ∀ n, 1 ≤ n → n ≤ R →
      F (n-1)*F (n+1)*fi (n+1)^2 ≤ F n^2*fi n*fi (n+2) := by
  intro n hn hnR
  have he0 : n-1+1=n := by omega
  have he2 : n+1+1=n+2 := by omega
  by_cases hearly : n ≤ h+1
  · have hp0 := hpre (n-1) (by omega)
    have hp1 := hpre n hearly
    rw [he0] at hp0
    rw [hp0,hp1]
    have hbn := hb (n+1)
    rw [he2] at hbn
    have hm := mul_le_mul_of_nonneg_left hbn
      (show 0 ≤ fi n*fi (n+1)^2 by unfold fi;positivity)
    nlinarith only [hm]
  have hn2 : 2 ≤ n := by omega
  have hm := hs n (by omega) (hg n hn2 hnR)
  have hc := cassini n
  have hsg := sign_bounds n
  have hbp := hb (n-1)
  have hbn := hb (n+1)
  rw [he0] at hbp
  rw [he2] at hbn
  have hub : F (n-1)*F (n+1) ≤ fi n*fi (n+2) :=
    mul_le_mul hbp hbn (hp _) (by unfold fi;positivity)
  have hr : 0 ≤ fi n*fi (n+2) := by unfold fi;positivity
  have ha := mul_nonneg hr (sub_nonneg.mpr hm)
  have hd := mul_nonneg (mul_nonneg (hp (n-1)) (hp (n+1)))
    (sub_nonneg.mpr (show fi (n+1)^2-fi n*fi (n+2) ≤ 1 by omega))
  dsimp [minor] at ha
  nlinarith only [ha,hd,hub]

theorem binary_ordinary_mode_count_bound (R : ℕ → ℕ)
    (h0 : R 0=0) (hstep : ∀ h, R (h+1) ≤ R h+2) :
    ∀ h, R h ≤ 2*h := by
  intro h
  induction h with
  | zero => simp [h0]
  | succ h ih => have hs := hstep h;omega

theorem shared_current_decrease_C (G Gprev Dprev D c : ℤ)
    (hGp : 0 ≤ Gprev) (hc : 0 ≤ c)
    (hC : Gprev*D ≤ G*Dprev) : Gprev*(D-c) ≤ G*Dprev := by
  have hmul := mul_nonneg hGp hc
  nlinarith only [hmul,hC]

theorem positive_support_outgoing_unit (x y M : ℤ)
    (hx : 0 ≤ x) (hM : 1 ≤ M) (hbound : x ≤ M)
    (hy : 0 ≤ y) (hunit : 0<x → 1 ≤ y) : x-y ≤ M-1 := by
  by_cases hz : x=0
  · omega
  · have hu := hunit (by omega);omega

#print axioms strict_binary_ordinary_boundary
#print axioms window_LC_strict_when_growing
#print axioms ordinary_binary_full_tail_induction
#print axioms ordinary_binary_relative_LC_prefix
#print axioms binary_ordinary_mode_count_bound
#print axioms shared_current_decrease_C
#print axioms positive_support_outgoing_unit
end BinaryOrdinaryTailAndOneJump
