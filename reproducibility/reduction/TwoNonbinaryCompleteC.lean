import Mathlib
set_option maxHeartbeats 1500000

namespace TwoNonbinaryCompleteC

theorem one_jump_golden_head_bounds (q e : ℝ)
    (hq0 : 0<q) (hq1 : q<1) (heq : q^2+q=1)
    (he0 : -q^3 ≤ e) (he1 : e ≤ q^3) :
    q^2 ≤ q+e ∧ q+e<1 := by
  have hc := congrArg (fun x : ℝ => x*q) heq
  have hid : q-q^3=q^2 := by nlinarith
  have hq23 : q<2/3 := by nlinarith
  constructor <;> nlinarith

theorem decaying_tail_below_head (q H T : ℝ)
    (hq0 : 0<q) (hH : H<1) (hT : T ≤ q^2*H) : T<q^2 := by nlinarith [sq_pos_of_pos hq0]

theorem exact_window_golden_payment (phi A B X0 X1 Y0 Y1 : ℝ)
    (hA : A=X0-Y0) (hB : B=X1-Y1)
    (hgap : X1-phi*X0<Y1-phi*Y0) : B<phi*A := by
  rw [hA,hB]
  nlinarith

theorem correct_binary_first_missing (L : ℕ) (hL : 3 ≤ L) :
    min (L+1) (3+1)=4 ∧ max 4 (min (L+1) (3+1)-1)=4 := by omega

theorem all_small_binary_residuals_excluded (u L t n : ℕ)
    (hu : u ≤ 4) (hL : 5 ≤ L) (ht : L ≤ t)
    (hmode : 2*n ≤ 3*u+L+2) : n ≤ t+4 := by omega

theorem surplus_residual_read_guards (u L t n : ℕ)
    (hL : 3 ≤ L) (ht : L ≤ t) (hu : L-1 ≤ u)
    (hstart : t+4<n) (hend : n<L+t) (hloss : u+3<n) :
    2 ≤ n-t-1 ∧ n-t-1 ≤ L-2 ∧ n-t-1 ≤ u+2 ∧
    max L (u+3) ≤ n-1 := by omega

theorem deficit_residual_read_guards (u L t n : ℕ)
    (ht : L ≤ t) (hu : u<L-1) (hstart : t+4<n) :
    2 ≤ n-t-1 ∧ max L (u+3) ≤ n-1 := by omega

theorem whole_ordinary_LC_prefix_tail_join (L : ℕ) (LC : ℕ → Prop)
    (hprefix : ∀ n,2 ≤ n → n<L → LC n)
    (htail : ∀ n,L-1 ≤ n → LC n) : ∀ n,2 ≤ n → LC n := by
  intro n hn
  by_cases h : n<L
  · exact hprefix n hn h
  · exact htail n (by omega)

theorem all_current_complete_C_assembly (u L t ell : ℕ) (C : ℕ → Prop)
    (ht : L ≤ t) (hell : 2*ell ≤ 3*u+L+2)
    (hprefix : ∀ n,n ≤ t+4 → C n)
    (hpost : ∀ n,ell<n → C n)
    (hlate : ∀ n,L+t ≤ n → C n)
    (hresidual : ∀ n,5 ≤ u → t+4<n → n<L+t → n ≤ ell → C n) :
    ∀ n,C n := by
  intro n
  by_cases hp : n ≤ t+4
  · exact hprefix n hp
  by_cases hl : L+t ≤ n
  · exact hlate n hl
  by_cases hm : ell<n
  · exact hpost n hm
  have hnmode : 2*n ≤ 3*u+L+2 := by omega
  have hL : 5 ≤ L := by omega
  have hu : 5 ≤ u := by
    by_contra hh
    have hx := all_small_binary_residuals_excluded u L t n (by omega) hL ht hnmode
    exact hp hx
  exact hresidual n hu (by omega) (by omega) (by omega)

#print axioms one_jump_golden_head_bounds
#print axioms decaying_tail_below_head
#print axioms exact_window_golden_payment
#print axioms correct_binary_first_missing
#print axioms all_small_binary_residuals_excluded
#print axioms surplus_residual_read_guards
#print axioms deficit_residual_read_guards
#print axioms whole_ordinary_LC_prefix_tail_join
#print axioms all_current_complete_C_assembly

end TwoNonbinaryCompleteC
