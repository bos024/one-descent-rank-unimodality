import Mathlib

set_option maxHeartbeats 0
namespace OneJumpUniformAnalyticKernels

private def fi (n : ℕ) : ℤ := Nat.fib n

private theorem sign_bounds (n : ℕ) : -1 ≤ (-1:ℤ)^n ∧ (-1:ℤ)^n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ];constructor <;> nlinarith [ih.1,ih.2]

theorem modified_first_two_defect_boundaries (h : ℕ) (hh : 2 ≤ h) :
    0 ≤ (-1:ℤ)^(h+2)-4*fi (h+3)+4+((h:ℤ)+3)*fi (h+2) ∧
    0 ≤ (-1:ℤ)^(h+2)-4*fi (h+3)+4+((h:ℤ)+4)*fi (h+2) ∧
    0 ≤ (-1:ℤ)^(h+2)-6*fi (h+3)+9+(2*(h:ℤ)+4)*fi (h+2) := by
  by_cases hsmall : h ≤ 4
  · interval_cases h <;> norm_num [fi]
  have hlarge : 5 ≤ h := by omega
  have hz : (5:ℤ) ≤ h := by exact_mod_cast hlarge
  have hy : 0 ≤ fi (h+2) := by unfold fi;positivity
  have hx : fi (h+3) ≤ 2*fi (h+2) := by
    have hm := Nat.fib_mono (show h+1 ≤ h+2 by omega)
    have hr := Nat.fib_add_two (n:=h+1)
    have he : h+1+2=h+3 := by omega
    rw [he] at hr
    rw [show h+1+1=h+2 by omega] at hr
    unfold fi
    exact_mod_cast (show Nat.fib (h+3) ≤ 2*Nat.fib (h+2) by omega)
  have hs := (sign_bounds (h+2)).1
  have hp := mul_nonneg (show 0 ≤ (h:ℤ)-5 by omega) hy
  constructor
  · nlinarith only [hp,hx,hs]
  constructor <;> nlinarith only [hp,hx,hs,hy]

theorem modified_LC_window_both_old_growing (A B C D : ℤ)
    (hA : 1 ≤ A) (hAB : A<B) (hBC : B<C)
    (_hLC1 : 0 ≤ B^2-A*C) (hLC2 : 0 ≤ C^2-B*D)
    (hS1 : A*(C-1) ≤ (B-1)^2) (hS2 : B*(D-1) ≤ (C-1)^2) :
    (A+B)*(C+D-1) ≤ (B+C-1)^2 := by
  have hm1 : 1 ≤ B^2-A*C := by nlinarith only [hS1,hA,hAB]
  have hm2 : 1 ≤ C^2-B*D := by nlinarith only [hS2,hA,hAB,hBC]
  have hp := mul_pos (show 0 < C by omega) (show 0 < B^2-A*C by omega)
  have hq := mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ C^2-B*D by omega)
  have hcpos : 0 < B*(B*C-A*D) := by nlinarith only [hp,hq]
  have hc : 1 ≤ B*C-A*D := by
    have hh : 0 < B*C-A*D :=
      (mul_pos_iff_of_pos_left (show 0 < B by omega)).mp hcpos
    omega
  nlinarith only [hS1,hS2,hc]

theorem modified_LC_window_old_turn (A B C D : ℤ)
    (hA : 0 ≤ A) (hC : A+1 ≤ C) (hB : C ≤ B) (hD : D ≤ C) :
    (A+B)*(C+D-1) ≤ (B+C-1)^2 := by
  have hprev : A+B ≤ B+C-1 := by omega
  have hnext : C+D-1 ≤ B+C-1 := by omega
  have hnon : 0 ≤ A+B := by omega
  have htop : 0 ≤ B+C-1 := by omega
  have h1 := mul_le_mul_of_nonneg_left hnext hnon
  have h2 := mul_le_mul_of_nonneg_right hprev htop
  nlinarith only [h1,h2]

theorem odd_Fibonacci_subtraction_LC (a A C b B d : ℤ)
    (hb : 1 ≤ b) (hab : b<a) (haA : a<A)
    (hstrong : a*(C-1) ≤ (A-1)^2) (hout : B^2-b*d=1) :
    (a-b)*(C-d) ≤ (A-B)^2 := by
  have hm : a+1 ≤ A^2-a*C := by nlinarith only [hstrong,haA]
  have hmnon : 0 ≤ A^2-a*C := by omega
  have hbmul := mul_nonneg (show 0 ≤ b-1 by omega) hmnon
  have hbudget : 0 ≤ b*(A^2-a*C)-a := by nlinarith only [hbmul,hm]
  have hp := mul_nonneg (show 0 ≤ a-b by omega) hbudget
  have hs := sq_nonneg (b*A-a*B)
  have hid : a*b*((A-B)^2-(a-b)*(C-d))=
      (a-b)*(b*(A^2-a*C)-a*(B^2-b*d))+(b*A-a*B)^2 := by ring
  rw [hout] at hid
  have hr : 0 ≤ a*b*((A-B)^2-(a-b)*(C-d)) := by nlinarith only [hp,hs,hid]
  have habpos : 0 < a*b := mul_pos (by omega) (by omega)
  have hres := (mul_nonneg_iff_of_pos_left habpos).mp hr
  nlinarith only [hres]

theorem first_notch_modified_LC (a A C : ℤ)
    (hstrong : a*(C-1) ≤ (A-1)^2) :
    a*(C-1) ≤ (A-1)^2 := hstrong

theorem local_valley_relative_LC_removal (p q w x u z : ℝ)
    (_hp : 0 ≤ p) (hp1 : p<1) (_hq : 0 ≤ q) (hqp : q ≤ p)
    (hw : 0 ≤ w) (hw1 : w<1) (hqw : q ≤ w)
    (hx0 : p ≤ x) (hx1 : x ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hz : z ≤ x*u^2) :
    (x-p)*(z-w)*(1-q)^2 ≤ (x*u-q)^2*(1-p)*(1-w) := by
  let P : ℝ → ℝ := fun y =>
    (y*u-q)^2*(1-p)*(1-w)-(y-p)*(y*u^2-w)*(1-q)^2
  let K : ℝ := u^2*((1-p)*(1-w)-(1-q)^2)
  let c0 : ℝ := q^2*(1-w)+w*(1-q)^2
  let c1 : ℝ := 2*(1-q)*(w-q)
  have hq1 : q ≤ 1 := by linarith
  have hpc : 0 ≤ 1-p := by linarith
  have hwc : 0 ≤ 1-w := by linarith
  have hqc : 0 ≤ 1-q := by linarith
  have hprod : (1-p)*(1-w) ≤ (1-q)^2 := by
    have hm := mul_le_mul (show 1-p ≤ 1-q by linarith)
      (show 1-w ≤ 1-q by linarith) hwc hqc
    nlinarith only [hm]
  have hK : K ≤ 0 := by
    dsimp [K]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) (by linarith)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact add_nonneg (mul_nonneg (sq_nonneg q) hwc) (mul_nonneg hw (sq_nonneg (1-q)))
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    exact mul_nonneg (mul_nonneg (by norm_num) hqc) (by linarith)
  have hPp : 0 ≤ P p := by
    dsimp [P]
    simp only [sub_self,zero_mul,sub_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hpc) hwc
  have hP1 : 0 ≤ P 1 := by
    have hid : P 1=(1-p)*(1-u)*((1-u)*c0+u*c1) := by dsimp [P,c0,c1];ring
    rw [hid]
    exact mul_nonneg (mul_nonneg hpc (by linarith))
      (add_nonneg (mul_nonneg (by linarith) hc0) (mul_nonneg hu0 hc1))
  have hchord : (1-p)*P x=(1-x)*P p+(x-p)*P 1-K*(1-p)*(x-p)*(1-x) := by
    dsimp [P,K];ring
  have hleft := mul_nonneg (show 0 ≤ 1-x by linarith) hPp
  have hright := mul_nonneg (show 0 ≤ x-p by linarith) hP1
  have hcurve : 0 ≤ -K*(1-p)*(x-p)*(1-x) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hpc) (by linarith)) (by linarith)
  have hPx : 0 ≤ P x := by
    have hh : 0 ≤ (1-p)*P x := by nlinarith only [hchord,hleft,hright,hcurve]
    exact (mul_nonneg_iff_of_pos_left (show 0 < 1-p by linarith)).mp hh
  have hcost := mul_nonneg
    (mul_nonneg (show 0 ≤ x-p by linarith) (show 0 ≤ x*u^2-z by linarith))
    (sq_nonneg (1-q))
  dsimp [P] at hPx
  nlinarith only [hPx,hcost]

def minor (a : ℕ → ℤ) (n : ℕ) : ℤ := a n^2-a (n-1)*a (n+1)

theorem whole_modified_binary_tail_induction (F : ℕ → ℕ → ℤ)
    (hp : ∀ h n, 0 ≤ F h n)
    (hz : ∀ h n, F h n=0 → F h (n+1)=0)
    (hrec : ∀ h n, 2 ≤ n → F (h+1) n=F h (n-1)+F h (n-2))
    (hLC : ∀ h n, 2 ≤ h → h+1 ≤ n → 0 ≤ minor (F h) n)
    (hfall : ∀ h n, 2 ≤ h → 2 ≤ n → F h (n+1) ≤ F h n →
      F h (n+2) ≤ F h (n+1))
    (hboundary : ∀ h, 2 ≤ h →
      F h (h+1)*(F h (h+3)-1) ≤ (F h (h+2)-1)^2)
    (hbase : ∀ n, 4 ≤ n → F 2 (n-1)<F 2 n → n=4) :
    ∀ h, 2 ≤ h → ∀ n, h+2 ≤ n → F h (n-1)<F h n →
      F h (n-1)*(F h (n+1)-1) ≤ (F h n-1)^2 := by
  intro h hh
  induction h, hh using Nat.le_induction with
  | base =>
    intro n hn hg
    have he := hbase n hn hg
    subst n
    exact hboundary 2 (by omega)
  | succ h hh ih =>
    intro n hn hg
    by_cases hb : n=h+3
    · subst n
      simpa using hboundary (h+1) (by omega)
    have hn4 : h+4 ≤ n := by omega
    have ep := hrec h (n-1) (by omega)
    have ec := hrec h n (by omega)
    have en := hrec h (n+1) (by omega)
    have ei1 : n-1-1=n-2 := by omega
    have ei2 : n-1-2=n-3 := by omega
    have ei3 : n+1-1=n := by omega
    have ei4 : n+1-2=n-1 := by omega
    rw [ei1,ei2] at ep
    rw [ei3,ei4] at en
    rw [ep,ec] at hg
    have hAC : F h (n-3)<F h (n-1) := by omega
    have hA : 1 ≤ F h (n-3) := by
      by_contra ha
      have hzero : F h (n-3)=0 := by have hp0 := hp h (n-3);omega
      have hz1 := hz h (n-3) hzero
      have ee1 : n-3+1=n-2 := by omega
      rw [ee1] at hz1
      have hz2 := hz h (n-2) hz1
      have ee2 : n-2+1=n-1 := by omega
      rw [ee2] at hz2
      omega
    have hi1 := hLC h (n-2) hh (by omega)
    have hi2 := hLC h (n-1) hh (by omega)
    have ei5 : n-2-1=n-3 := by omega
    have ei6 : n-2+1=n-1 := by omega
    have ei7 : n-1+1=n := by omega
    dsimp [minor] at hi1 hi2
    rw [ei5,ei6] at hi1
    rw [ei1,ei7] at hi2
    have hres : (F h (n-3)+F h (n-2))*(F h (n-1)+F h n-1) ≤
        (F h (n-2)+F h (n-1)-1)^2 := by
      by_cases hBC : F h (n-2)<F h (n-1)
      · have hB : 0 < F h (n-2) := by
          by_contra hb0
          have hbn := hp h (n-2)
          have hbz : F h (n-2)=0 := by omega
          have hcpos : 0 < F h (n-1) := by omega
          have hm := mul_pos (show 0 < F h (n-3) by omega) hcpos
          rw [hbz] at hi1
          nlinarith only [hi1,hm]
        have hAB : F h (n-3)<F h (n-2) := by
          by_contra hab
          have hhAB : 0 ≤ F h (n-3)-F h (n-2) := by omega
          have hp1 := mul_nonneg hhAB (hp h (n-1))
          have hp2 := mul_pos hB (show 0 < F h (n-1)-F h (n-2) by omega)
          nlinarith only [hi1,hp1,hp2]
        have hs1 := ih (n-2) (by omega) hAB
        have hs2 := ih (n-1) (by omega) hBC
        rw [ei5,ei6] at hs1
        rw [ei1,ei7] at hs2
        exact modified_LC_window_both_old_growing _ _ _ _ hA hAB hBC hi1 hi2 hs1 hs2
      · have hf := hfall h (n-2) hh (by omega) (by simpa only [ei6] using le_of_not_gt hBC)
        have ei8 : n-2+2=n := by omega
        rw [ei6,ei8] at hf
        exact modified_LC_window_old_turn _ _ _ _ (hp _ _) (by omega) (by omega) hf
    rw [ep,ec,en]
    nlinarith only [hres]

private theorem window_LC (A B C D : ℤ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 < B)
    (h1 : 0 ≤ B^2-A*C) (h2 : 0 ≤ C^2-B*D) :
    0 ≤ (B+C)^2-(A+B)*(C+D) := by
  have hp := mul_nonneg hC h1
  have hq := mul_nonneg hA h2
  have hc : 0 ≤ B*C-A*D := by
    have hh : 0 ≤ B*(B*C-A*D) := by nlinarith only [hp,hq]
    exact (mul_nonneg_iff_of_pos_left hB).mp hh
  nlinarith only [h1,h2,hc]

theorem whole_rising_reference_tail_induction
    (d : ℕ → ℕ → ℤ) (E : ℕ → ℕ) (r : ℕ → ℤ) (H : ℕ)
    (hH : 2 ≤ H) (hp : ∀ h n, 0 ≤ d h n)
    (hz : ∀ h n, d h n=0 → d h (n+1)=0)
    (hmax : ∀ h n, d h n ≤ d h (E h))
    (hpost : ∀ h i j, E h ≤ i → i ≤ j → d h j ≤ d h i)
    (hstrict : ∀ h n, H ≤ h → h ≤ n → n<E h → d h n<d h (n+1))
    (hr : ∀ n, 0 ≤ r n)
    (hpre : ∀ h n, H ≤ h → n ≤ h → d h n=r n)
    (hdef : ∀ h, H ≤ h → d h (h+1) ≤ r (h+1)-1)
    (hboundary : ∀ h, H ≤ h → 0 ≤ r h^2-r (h-1)*(r (h+1)-1))
    (heq : ∀ h n, H ≤ h → h+1 ≤ n → n<E (h+1) →
      d (h+1) n=d h (n-1)+d h (n-2))
    (hle : ∀ h n, H ≤ h → h+1 ≤ n →
      d (h+1) n ≤ d h (n-1)+d h (n-2))
    (hbase : ∀ n, H ≤ n → n ≤ E H → 0 ≤ minor (d H) n) :
    ∀ h, H ≤ h → ∀ n, h ≤ n → n ≤ E h → 0 ≤ minor (d h) n := by
  intro h hh
  induction h, hh using Nat.le_induction with
  | base => exact hbase
  | succ h hh ih =>
    intro n hn hnE
    have hn3 : 3 ≤ n := by omega
    by_cases hpeak : n=E (h+1)
    · have hprev := hmax (h+1) (n-1)
      have hnext := hmax (h+1) (n+1)
      rw [← hpeak] at hprev hnext
      have hm := mul_le_mul hprev hnext (hp _ _) (hp _ _)
      dsimp [minor]
      nlinarith only [hm]
    have hnlt : n<E (h+1) := by omega
    by_cases hb : n=h+1
    · subst n
      have hp0 := hpre (h+1) h (by omega) (by omega)
      have hp1 := hpre (h+1) (h+1) (by omega) (by omega)
      have hd := hdef (h+1) (by omega)
      have hm := mul_le_mul_of_nonneg_left hd (hr h)
      have hs := hboundary (h+1) (by omega)
      have eidx : h+1-1=h := by omega
      rw [eidx] at hs
      dsimp [minor]
      rw [hp0,hp1]
      nlinarith only [hm,hs]
    have ep := heq h (n-1) hh (by omega) (by omega)
    have ec := heq h n hh (by omega) hnlt
    have en := hle h (n+1) hh (by omega)
    have ei1 : n-1-1=n-2 := by omega
    have ei2 : n-1-2=n-3 := by omega
    have ei3 : n+1-1=n := by omega
    have ei4 : n+1-2=n-1 := by omega
    rw [ei1,ei2] at ep
    rw [ei3,ei4] at en
    have hg := hstrict (h+1) n (by omega) hn hnlt
    have hlift : d h (n-2)<d h n := by rw [ec] at hg;nlinarith only [hg,en]
    have hmE : n-1 ≤ E h := by
      by_contra he
      have ht := hpost h (n-2) n (by omega) (by omega)
      omega
    have hi1 := ih (n-2) (by omega) (by omega)
    have hi2 := ih (n-1) (by omega) hmE
    have ei5 : n-2-1=n-3 := by omega
    have ei6 : n-2+1=n-1 := by omega
    have ei7 : n-1+1=n := by omega
    dsimp [minor] at hi1 hi2
    rw [ei5,ei6] at hi1
    rw [ei1,ei7] at hi2
    have hB : 0 < d h (n-2) := by
      by_contra hb0
      have hbn := hp h (n-2)
      have hbz : d h (n-2)=0 := by omega
      have hz1 := hz h (n-2) hbz
      rw [ei6] at hz1
      have hz2 := hz h (n-1) hz1
      rw [ei7] at hz2
      omega
    have hw := window_LC _ _ _ _ (hp _ _) (hp _ _) hB hi1 hi2
    have hm := mul_le_mul_of_nonneg_left en
      (show 0 ≤ d h (n-2)+d h (n-3) by have hp1 := hp h (n-2);have hp2 := hp h (n-3);omega)
    dsimp [minor]
    rw [ep,ec]
    nlinarith only [hw,hm]

#print axioms modified_first_two_defect_boundaries
#print axioms modified_LC_window_both_old_growing
#print axioms modified_LC_window_old_turn
#print axioms odd_Fibonacci_subtraction_LC
#print axioms local_valley_relative_LC_removal
#print axioms whole_modified_binary_tail_induction
#print axioms whole_rising_reference_tail_induction
end OneJumpUniformAnalyticKernels
