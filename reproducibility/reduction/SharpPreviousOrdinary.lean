import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

namespace SharpPreviousOrdinary

theorem one_earlier_crossing_guards (u h r t a L b : ℕ)
    (hu : 5 ≤ u) (hr : 1 ≤ r) (hhlo : 2*r ≤ h) (hhhi : h ≤ u)
    (ha : a=h+r) (hL : L=u+r+1) (hb : b=a+t)
    (hcross : u+3 ≤ h+t) :
    2 ≤ a-1 ∧ a+1 ≤ L ∧ L+1 ≤ b-1 ∧ 6 ≤ u+r := by omega

theorem head_plus_tail_dominance (q Hprev Hlast diff : ℝ)
    (hq : 0<q) (hp : 0<Hprev) (hl : 0<Hlast)
    (hbound : Hprev+q^2*Hlast ≤ diff) : 0<diff := by
  nlinarith [mul_pos (sq_pos_of_pos hq) hl]

theorem reference_previous_ordinary_minor (x y A : ℝ)
    (hA : A=x^2+x*y-y^2) (hpay : A ≤ x+y) :
    0 ≤ y^2-(x-1)*(x+y) := by nlinarith

theorem nonincreasing_positive_slopes_LC (prev cur next a b : ℝ)
    (hp : 0 ≤ prev) (ha : a=cur-prev) (hb : b=next-cur)
    (hdec : b ≤ a) :
    a^2 ≤ cur^2-prev*next := by
  have h := mul_nonneg hp (show 0 ≤ a-b by linarith)
  rw [ha,hb] at h
  rw [ha]
  nlinarith

theorem binary_cumulative_first_defect_seed (A B C delta : ℝ)
    (hA : 0 ≤ A) (hd : 0 ≤ delta) (hlc : A*C ≤ B^2) :
    A*(C-delta) ≤ B^2 := by
  nlinarith [mul_nonneg hA hd]

theorem local_window_LC_read_guards (a t n : ℕ) (ht : 1 ≤ t)
    (ha : 2 ≤ a) (hn : a+t-1 ≤ n) :
    a-1 ≤ n-t ∧ a-2 ≤ n-1-t := by omega

theorem sharp_triple_minor_identity (x y k eps : ℝ)
    (hcassini : y^2-x^2-x*y=eps) (hlinear : 3*x-2*y=-k) :
    (2*y-3)^2-(2*x-2)*(2*(x+y)-4)=1-4*k+4*eps := by nlinarith

theorem sharp_minor_negative_all_capacities (T : ℕ) (hT : 4 ≤ T) :
    1-4*(Nat.fib (T-2):ℝ)+4*(-1:ℝ)^(T+1)<0 := by
  by_cases h4 : T=4
  · subst T; norm_num
  · have hf : 2 ≤ Nat.fib (T-2) := by
      have hh := Nat.fib_mono (show 3 ≤ T-2 by omega)
      norm_num at hh ⊢
      exact hh
    have hfR : (2:ℝ) ≤ (Nat.fib (T-2):ℝ) := by exact_mod_cast hf
    have he : (-1:ℝ)^(T+1) ≤ 1 := by
      calc
        (-1:ℝ)^(T+1) ≤ |(-1:ℝ)^(T+1)| := le_abs_self _
        _=1 := by simp
    nlinarith

theorem sharp_triple_strict_growth (x y : ℝ) (hx : 1 ≤ x) (hy : x+1 ≤ y) :
    2*x-2<2*y-3 ∧ 2*y-3<2*(x+y)-4 := by constructor <;> linarith

theorem binary_reference_CDF_minor (x y k eps : ℝ)
    (hrec : 2*x-y=k) (hcassini : y^2-x*(x+y)=eps) :
    (y-1)^2-(x-1)*(x+y-1)=k+eps := by nlinarith

#print axioms one_earlier_crossing_guards
#print axioms head_plus_tail_dominance
#print axioms reference_previous_ordinary_minor
#print axioms nonincreasing_positive_slopes_LC
#print axioms binary_cumulative_first_defect_seed
#print axioms local_window_LC_read_guards
#print axioms sharp_triple_minor_identity
#print axioms sharp_minor_negative_all_capacities
#print axioms sharp_triple_strict_growth
#print axioms binary_reference_CDF_minor

end SharpPreviousOrdinary

