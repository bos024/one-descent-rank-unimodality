import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

namespace HereditaryStrongLateC

theorem golden_margin_constants (q : ℝ) (_hq0 : 0≤q) (hq : q≤5/8)
    (heq : q^2+q=1) : 0≤q^2 ∧ 2*q^2≥q ∧ 2-(q+1)=q^2 := by
  constructor
  · positivity
  constructor <;> nlinarith

theorem binary_cumulative_gap_box (q : ℝ) (K : ℕ → ℝ)
    (hq0 : 0≤q) (_hq1 : q≤1) (heq : q^2+q=1)
    (h0 : K 0=1) (hs : ∀ n, K (n+1)=1-q*K n) :
    ∀ n, q^2≤K n ∧ K n≤1 := by
  intro n
  induction n with
  | zero => rw [h0]; constructor <;> nlinarith
  | succ n ih =>
      rw [hs]
      have h1 := mul_nonneg hq0 (show 0≤1-K n by linarith)
      have h2 := mul_nonneg hq0 (show 0≤K n by nlinarith [sq_nonneg q])
      constructor <;> nlinarith

theorem all_length_tail_window_margin (q mu : ℝ) (t : ℕ)
    (_hq : 0≤q) (_heq : q^2+q=1) (hpay : q≤2*q^2)
    (hmu : mu≤q+1) (ht : 3≤t) :
    q^2≤1-mu+(t:ℝ)*q^2 := by
  have htR : 3≤(t:ℝ) := by exact_mod_cast ht
  have h := mul_nonneg (show 0≤(t:ℝ)-3 by linarith) (sq_nonneg q)
  nlinarith

theorem head_window_atom_margin (q mu S : ℝ) (heq : q^2+q=1)
    (hmu : mu≤q+1) (hS : 1≤S) : q^2≤1-mu+S := by nlinarith

theorem finite_window_residual_sum (I : Finset ℕ) (A B : ℕ → ℝ)
    (mu : ℝ) :
    (1+∑ i ∈ I, A i)-mu*(1+∑ i ∈ I, B i)
      =1-mu+∑ i ∈ I, (A i-mu*B i) := by
  rw [Finset.sum_sub_distrib,mul_add,Finset.mul_sum]
  ring

theorem adjacent_ratio_antitone (R : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ n, n<K → R (n+1)≤R n) :
    ∀ i j, i≤j → j≤K → R j≤R i := by
  intro i j hij hjK
  induction hij with
  | refl => exact le_rfl
  | @step j hij ih =>
      exact le_trans (hstep j (by omega)) (ih (by omega))

theorem positive_LC_adjacent_ratio (a b c : ℝ) (ha : 0<a) (hb : 0<b)
    (hlc : a*c≤b^2) : c/b≤b/a := by
  apply (div_le_div_iff₀ hb ha).2
  nlinarith

theorem subtracted_window_ratio (A B leftPrev left rightPrev right : ℝ)
    (hA : A=rightPrev-leftPrev) (hB : B=right-left)
    (hc : right*leftPrev≤left*rightPrev) :
    B*rightPrev≤A*right := by
  rw [hA,hB]
  nlinarith

theorem all_prefix_ratio_lower (R : ℕ → ℝ) (K : ℕ) (mu : ℝ)
    (hstep : ∀ n, n<K → R (n+1)≤R n) (hmu : mu≤R K) :
    ∀ i, i≤K → mu≤R i := by
  intro i hi
  exact le_trans hmu (adjacent_ratio_antitone R K hstep i K hi (le_refl K))

theorem full_mode_ratio_cap (R : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ n, n<K → R (n+1)≤R n)
    (hpost : ∀ n, K≤n → R n≤1) :
    ∀ n, R n ≤ max 1 (R 0) := by
  intro n
  by_cases hn : n≤K
  · exact le_trans (adjacent_ratio_antitone R K hstep 0 n (Nat.zero_le n) hn) (le_max_right _ _)
  · exact le_trans (hpost n (by omega)) (le_max_left _ _)

theorem weighted_window_ratio_cap (I : Finset ℕ) (d e : ℕ → ℝ)
    (A B cap : ℝ) (hA : A=∑ i ∈ I,d i) (hB : B=∑ i ∈ I,e i)
    (hstep : ∀ i ∈ I, e i≤cap*d i) : B≤cap*A := by
  rw [hA,hB,Finset.mul_sum]
  exact Finset.sum_le_sum hstep

theorem rising_window_forces_rising_seed (A B seed : ℝ)
    (_hA : 0<A) (hg : A<B) (hcap : B ≤ max 1 seed*A) :
    1<seed ∧ B ≤ seed*A := by
  have hs : 1<seed := by
    by_contra hn
    have hh : seed≤1 := by linarith
    rw [max_eq_left hh] at hcap
    nlinarith
  constructor
  · exact hs
  · simpa [max_eq_right (le_of_lt hs)] using hcap

theorem cumulative_margin_prefix_extension (R E : ℕ → ℝ) (c : ℝ)
    (h0 : c≤R 0) (hs : ∀ n,R (n+1)=R n+E n) (hE : ∀ n,0≤E n) :
    ∀ n,c≤R n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs]; linarith [hE n]

theorem smaller_ratio_preserves_margin (G Gprev mu lam c : ℝ)
    (hp : 0≤Gprev) (hm : mu≤lam) (hgap : c≤G-lam*Gprev) :
    c≤G-mu*Gprev := by
  nlinarith [mul_nonneg (show 0≤lam-mu by linarith) hp]

theorem first_crossing_prefix (xs : List ℕ) (K d : ℕ)
    (hK : 1≤K) (hbound : ∀ x∈xs,x≤d) (hmass : K≤xs.sum) :
    ∃ p s, xs=p++s ∧ K≤p.sum ∧ p.sum≤K+d-1 := by
  induction xs generalizing K with
  | nil => simp only [List.sum_nil] at hmass; omega
  | cons a xs ih =>
      by_cases ha : K≤a
      · refine ⟨[a],xs,?_,?_,?_⟩
        · simp
        · simpa using ha
        · have had := hbound a (by simp)
          simp only [List.sum_singleton]
          omega
      · have hb : ∀ x∈xs,x≤d := by
          intro x hx
          exact hbound x (by simp [hx])
        have hm : K-a≤xs.sum := by simp only [List.sum_cons] at hmass; omega
        obtain ⟨p,s,he,hlo,hhi⟩ := ih (K-a) (by omega) hb hm
        refine ⟨a::p,s,?_,?_,?_⟩
        · simp [he]
        · simp only [List.sum_cons]; omega
        · simp only [List.sum_cons]; omega

theorem prefix_sum_length_bound (xs : List ℕ) (d : ℕ)
    (hb : ∀ x∈xs,x≤d) : xs.sum≤xs.length*d := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := hb a (by simp)
      have ht : ∀ x∈xs,x≤d := by intro x hx; exact hb x (by simp [hx])
      have hh := ih ht
      simp only [List.sum_cons,List.length_cons,Nat.add_mul]
      omega

theorem bounded_crossing_has_two_factors (u d r h : ℕ)
    (hu : 33≤u) (hd : 13*d≤4*u+38) (hh : u+1≤h) (hb : h≤r*d) :
    2≤r := by
  by_contra hn
  have hr : r≤1 := by omega
  have hrp : r*d≤d := by nlinarith
  omega

theorem crossing_prefix_in_new_cone (u d r h : ℕ)
    (hu : 33≤u) (hr : 2≤r) (hd : 13*d≤4*u+38)
    (hlo : u+1≤h) (hhi : h≤u+d) :
    13*h≤17*u+4*r+30 ∧ 33≤h+r := by omega

theorem unresolved_crossing_at_most_six_suffix_factors (u r d m : ℕ)
    (hu : 33≤u) (hr : 2≤r)
    (hjump : 4*u+4*r+30<13*d)
    (hdegree : u+1+m*d≤3*u-2) : m≤6 := by
  by_contra hm
  have hseven : 7*d ≤ m*d := Nat.mul_le_mul_right d (by omega)
  omega

theorem single_crossing_at_most_one_suffix_factor (u d m : ℕ)
    (hcross : u+1≤d) (hdegree : (m+1)*d≤3*u-2) : m≤1 := by
  by_contra hm
  have hthree : 3*d≤(m+1)*d := Nat.mul_le_mul_right d (by omega)
  omega

theorem one_gap_ordinary_seed (x y c A : ℝ) (hy : 0<y) (hc : 0<c)
    (hA : 0<A) (hdef : A=x^2+x*y-y^2) :
    0<x*(x+y)-(y-c)*y := by nlinarith [mul_pos hy hc]

theorem two_gap_ordinary_seed (x y b c A : ℝ)
    (hx : 0≤x) (hy : x≤y) (hb : 0<b) (hc : 3*b≤c)
    (hA : 0<A) (hdef : A=x^2+x*y-y^2) :
    A+b^2≤(x-b)*(x+y-b)-(y-c)*y ∧
    0<(x-b)*(x+y-b)-(y-c)*y := by
  have h1 := mul_nonneg (show 0≤y-x by linarith) (show 0≤c-b by linarith)
  have h2 := mul_nonneg hx (show 0≤c-3*b by linarith)
  constructor <;> nlinarith

theorem two_gap_all_padding_losses (w : ℝ) (hw : 3≤w) :
    3*2≤2*w+1 ∧ 3*1≤w+2 ∧ 3*1≤w+1 := by constructor <;> (try constructor) <;> linarith

theorem low_gap_golden_ceiling (p b c g : ℝ) (hp : p≤13/8)
    (hb : 0<b) (hc : 3*b≤c) (hg : 0<g) : 0<g+c-p*b := by
  have h := mul_nonneg (show 0≤13/8-p by linarith) (le_of_lt hb)
  nlinarith

#print axioms golden_margin_constants
#print axioms binary_cumulative_gap_box
#print axioms all_length_tail_window_margin
#print axioms head_window_atom_margin
#print axioms finite_window_residual_sum
#print axioms adjacent_ratio_antitone
#print axioms positive_LC_adjacent_ratio
#print axioms subtracted_window_ratio
#print axioms all_prefix_ratio_lower
#print axioms full_mode_ratio_cap
#print axioms weighted_window_ratio_cap
#print axioms rising_window_forces_rising_seed
#print axioms cumulative_margin_prefix_extension
#print axioms smaller_ratio_preserves_margin
#print axioms first_crossing_prefix
#print axioms prefix_sum_length_bound
#print axioms bounded_crossing_has_two_factors
#print axioms crossing_prefix_in_new_cone
#print axioms unresolved_crossing_at_most_six_suffix_factors
#print axioms single_crossing_at_most_one_suffix_factor
#print axioms one_gap_ordinary_seed
#print axioms two_gap_ordinary_seed
#print axioms two_gap_all_padding_losses
#print axioms low_gap_golden_ceiling

end HereditaryStrongLateC

