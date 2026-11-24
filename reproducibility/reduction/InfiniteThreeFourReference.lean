import Mathlib
set_option maxHeartbeats 4000000
namespace InfiniteThreeFourReference

theorem exact_quadratic_norm_contraction (a b x y : ℝ) :
    (-a*x-b*y)^2+a*(-a*x-b*y)*x+b*x^2=b*(x^2+a*x*y+b*y^2) := by ring

theorem entire_residual_quadratic_norm (a b : ℝ) (e : ℕ → ℝ)
    (h0 : e 0=1) (h1 : e 1= -a)
    (hr : ∀ n,e (n+2)= -a*e (n+1)-b*e n) :
    ∀ n,e (n+1)^2+a*e (n+1)*e n+b*e n^2=b^(n+1) := by
  intro n
  induction n with
  | zero => rw [h0,h1]; ring
  | succ n ih =>
    change e (n+2)^2+a*e (n+2)*e (n+1)+b*e (n+1)^2=b^(n+2)
    rw [hr,exact_quadratic_norm_contraction,ih]
    ring

theorem whole_norm_coercivity_and_absolute_bound (a b : ℝ) (e : ℕ → ℝ)
    (hb : 1/2≤b) (hb1 : b≤1) (ha : a^2≤3/4) (h0 : e 0=1)
    (hnorm : ∀ n,e (n+1)^2+a*e (n+1)*e n+b*e n^2=b^(n+1)) :
    ∀ n,|e n|≤2*b^(n/2) := by
  have coercive : ∀ x y : ℝ,(x^2+y^2)/4≤x^2+a*x*y+b*y^2 := by
    intro x y
    have p := mul_nonneg (show 0≤b-1/2 by linarith) (sq_nonneg y)
    have q := mul_nonneg (show 0≤3/4-a^2 by linarith) (sq_nonneg x)
    nlinarith only [p,q,sq_nonneg (y/2+a*x)]
  intro n
  have hb0 : 0≤b := by linarith
  have he2 : e n^2≤4*b^n := by
    cases n with
    | zero => simp [h0]
    | succ n =>
      have h := coercive (e (n+1)) (e n)
      rw [hnorm] at h
      nlinarith only [h,sq_nonneg (e n)]
  have hp : b^n≤b^(2*(n/2)) :=
    pow_le_pow_of_le_one hb0 hb1 (by omega)
  have hid : b^(2*(n/2))=(b^(n/2))^2 := by
    rw [Nat.mul_comm 2 (n/2),pow_mul]
  rw [hid] at hp
  apply abs_le_of_sq_le_sq _ (by positivity)
  nlinarith only [he2,hp]

theorem ordinary_minor_from_absolute_residuals (H e f l B : ℝ)
    (hH : 1≤H) (hL : 0≤l) (hL2 : l≤2)
    (hB : 0≤B) (hB1 : B≤1) (he : |e|≤2*B) (hf : |f|≤2*B) :
    |e^2+H*(l*e-f)|≤10*H*B := by
  have ee := abs_le.mp he
  have ff := abs_le.mp hf
  have ep := mul_nonneg (show 0≤2*B-e by linarith) (show 0≤2*B+e by linarith)
  have BB := mul_nonneg hB (show 0≤1-B by linarith)
  have el := mul_le_mul_of_nonneg_left ee.1 hL
  have eu := mul_le_mul_of_nonneg_left ee.2 hL
  have lb := mul_nonneg (show 0≤2-l by linarith) hB
  have wlow : -6*B≤l*e-f := by nlinarith only [el,ff.2,lb]
  have whigh : l*e-f≤6*B := by nlinarith only [eu,ff.1,lb]
  have H0 : 0≤H := by linarith
  have wl := mul_le_mul_of_nonneg_left wlow H0
  have wu := mul_le_mul_of_nonneg_left whigh H0
  have HB := mul_nonneg (show 0≤H-1 by linarith) hB
  apply abs_le.mpr
  constructor <;> nlinarith only [ep,BB,wl,wu,HB,sq_nonneg e]

theorem whole_scaled_minor_decay_payment (b : ℝ) (s n : ℕ)
    (hb : 1/2 ≤ b) (hb6 : b ≤ 6/11) (hs : 22 ≤ s) (hn : 3*s ≤ n+5) :
    10*(2:ℝ)^s*b^(n/2) < 1 := by
  have hb0 : 0≤b := by linarith
  have hb1 : b≤1 := by linarith
  have hexp : 3*s≤2*(n/2)+6 := by omega
  have hp := pow_le_pow_of_le_one hb0 hb1 hexp
  have hid : b^(2*(n/2)+6)=(b^(n/2))^2*b^6 := by
    rw [pow_add,Nat.mul_comm 2 (n/2),pow_mul]
  rw [hid] at hp
  have h2 : ((2:ℝ)^s)^2=(4:ℝ)^s := by
    simp only [sq,← mul_pow]; norm_num
  have hscaled : (((2:ℝ)^s*b^(n/2))^2)*b^6≤(4*b^3)^s := by
    rw [mul_pow,h2,mul_pow]
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤(4:ℝ)^s by positivity)
    rw [pow_mul] at hh
    nlinarith only [hh]
  have bmin : (1/64:ℝ)≤b^6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hb 6
    norm_num at h
    exact h
  have qmax : 4*b^3≤(2/3:ℝ) := by
    have h := pow_le_pow_left₀ hb0 hb6 3
    nlinarith only [h]
  have hq : (4*b^3)^s≤(2/3:ℝ)^22 := by
    apply le_trans (pow_le_pow_left₀ (by positivity) qmax s)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hmin := mul_le_mul_of_nonneg_left bmin (sq_nonneg ((2:ℝ)^s*b^(n/2)))
  have hsquare : (10*((2:ℝ)^s*b^(n/2)))^2<1 := by
    have hnum : (6400:ℝ)*(2/3:ℝ)^22<1 := by norm_num
    nlinarith only [hscaled,hq,hmin,hnum]
  nlinarith only [hsquare,sq_nonneg (10*((2:ℝ)^s*b^(n/2))-1)]

theorem complete_four_corner_polynomial_budgets (s : ℝ) (hs : 6 ≤ s) :
    let a1 := s-2
    let a2 := (s-1)*(s-2)/2
    let a3 := s*(s-1)*(s-2)/6+2
    0≤a1 ∧ 0≤a2 ∧ 0≤a3 ∧ 2*a1+1≤a2 ∧ 2*a2+1≤a3 ∧
    0≤a1^2-a2 ∧ 0≤a2^2-a3*a1 := by
  dsimp
  let x := s-6
  have hx : 0≤x := by dsimp [x]; linarith
  have hsx : s=6+x := by dsimp [x]; ring
  rw [hsx]
  constructor
  · linarith
  · constructor
    · ring_nf; positivity
    · constructor
      · ring_nf; positivity
      · constructor
        · have h : 0≤x^2/2+5*x/2+1 := by positivity
          nlinarith only [h]
        · constructor
          · have h : 0≤x^3/6+3*x^2/2+10*x/3+1 := by positivity
            nlinarith only [h]
          · constructor
            · ring_nf; positivity
            · ring_nf; positivity

theorem generic_corrected_tail_corner (A H K L a b c : ℝ)
    (hA : 0≤A) (hH : 0≤H) (hHK : H≤K) (hKL : K≤L)
    (hb : 0≤b) (hc : 0≤c) (ha : 2*b+1≤a)
    (hM : -H≤A*(K^2-H*L)) (hminor : 0≤b^2-a*c) :
    0≤(A*K-b)^2-(A*H-a)*(A*L-c) := by
  have h0 := mul_nonneg (show 0≤a-2*b-1 by linarith) (show 0≤L by linarith)
  have h1 := mul_nonneg hb (show 0≤L-K by linarith)
  have h2 := mul_nonneg hc hH
  have hbudget : H≤a*L+c*H-2*b*K := by nlinarith only [h0,h1,h2,hHK,hKL]
  have h3 := mul_nonneg hA (show 0≤a*L+c*H-2*b*K-H by linarith)
  have h4 := mul_nonneg hA (show 0≤A*(K^2-H*L)+H by linarith)
  nlinarith only [h3,h4,hminor]

theorem cumulative_negative_constant_improves_minor (A c x y z : ℝ)
    (hA : 0≤A) (hc : 0≤c) (hlc : 0≤y^2-x*z) (hconvex : 2*y≤x+z) :
    0≤(A*y-c)^2-(A*x-c)*(A*z-c) := by
  have h0 := mul_nonneg (sq_nonneg A) hlc
  have h1 := mul_nonneg (mul_nonneg hA hc) (show 0≤x+z-2*y by linarith)
  nlinarith only [h0,h1]

theorem coupled_negative_constant_preserves_comparison (A c d e x y : ℝ)
    (hA : 0≤A) (hc : 0≤c) (hd : 0≤d) (_he : 0≤e)
    (hxy : x≤y) (hx : 0≤A*x-c) (hC : d*y-e*x≥0) :
    0≤(A*d)*(A*y-c)-(A*e)*(A*x-c) := by
  by_cases hde : d≤e
  · have h0 := mul_nonneg (sq_nonneg A) hC
    have h1 := mul_nonneg (mul_nonneg hA hc) (show 0≤e-d by linarith)
    nlinarith only [h0,h1]
  · have h0 := mul_nonneg (mul_nonneg hA (show 0≤d-e by linarith)) hx
    have h1 := mul_nonneg (mul_nonneg hA hd) (show 0≤A*(y-x) by positivity)
    nlinarith only [h0,h1]

def cseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 1
  | s+1 => (1-z-z^2-z^3)+(z+z^2+z^3+z^4)*cseq z s
def jseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 0
  | s+1 => 1+(z+z^2+z^3+z^4)*jseq z s-z*(2*z)^s
theorem whole_reference_tail_polynomial_identity {R : Type*} [CommRing R]
    (z : R) : ∀ s : ℕ,cseq z s=(2*z)^s+(1-z-z^2-z^3)*jseq z s := by
  intro s
  induction s with
  | zero => simp [cseq,jseq]
  | succ s ih => simp only [cseq,jseq,ih,pow_succ]; ring

theorem source_constant_and_tail_mean (v : ℝ) (hv : 2≤v) :
    0≤(v-1)*(v-2)/6 ∧ (3*v-v^2-2)/6= -(v-1)*(v-2)/6 := by
  have h := mul_nonneg (show 0≤v-1 by linarith) (show 0≤v-2 by linarith)
  constructor
  · nlinarith only [h]
  · ring

theorem cubic_reciprocal_root_rational_interval (b : ℝ)
    (hb : 0≤b) (hroot : b^3+b^2+b=1) : 27/50<b ∧ b<6/11 := by
  have monotone : ∀ x y : ℝ,0≤x → 0≤y → x≤y →
      x^3+x^2+x≤y^3+y^2+y := by
    intro x y hx hy hxy
    have h2 := pow_le_pow_left₀ hx hxy 2
    have h3 := pow_le_pow_left₀ hx hxy 3
    linarith
  constructor
  · by_contra h
    have hh := monotone b (27/50) hb (by norm_num) (by linarith)
    norm_num at hh
    linarith
  · by_contra h
    have hh := monotone (6/11) b (by norm_num) hb (by linarith)
    norm_num at hh
    linarith

theorem cumulative_log_concavity_entry_step (a b c G : ℝ)
    (ha : 0<a) (hb : 0≤b) (hG : 0≤G)
    (hentry : b*(G-a)≤a*G) (hlc : a*c≤b^2) :
    0≤(G+b)^2-G*(G+b+c) := by
  have h0 := mul_le_mul_of_nonneg_right hentry hb
  have h1 := mul_le_mul_of_nonneg_right hlc hG
  have hh : 0≤a*((G+b)^2-G*(G+b+c)) := by
    nlinarith only [h0,h1]
  nlinarith only [hh,ha]

theorem exact_one_unit_cumulative_boundary_payment (A c d e x y : ℝ)
    (hA : 0≤A) (hc : 3≤c) (_hd : 0≤d) (he : 0≤e)
    (hgrow : 3*d≤2*e) (hC : 0≤d*y-e*x) :
    0≤(A*d)*(A*y-c)-(A*e)*(A*x-c+1) := by
  have hgap : 0≤e-d := by linarith
  have h0 := mul_nonneg (show 0≤c-3 by linarith) hgap
  have h1 := mul_nonneg hA (show 0≤c*(e-d)-e by nlinarith only [h0,hgrow])
  have h2 := mul_nonneg (sq_nonneg A) hC
  nlinarith only [h1,h2]

theorem whole_nonnegative_three_step_recurrence (v : ℕ → ℝ)
    (h0 : 0≤v 0) (h1 : 0≤v 1) (h2 : 0≤v 2)
    (hr : ∀ n,v (n+3)=v n+v (n+1)+v (n+2)) : ∀ n,0≤v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<3
    · interval_cases n <;> assumption
    · have hh : n=(n-3)+3 := by omega
      rw [hh,hr]
      exact add_nonneg (add_nonneg (ih (n-3) (by omega))
        (ih (n-3+1) (by omega))) (ih (n-3+2) (by omega))

#print axioms exact_quadratic_norm_contraction
#print axioms entire_residual_quadratic_norm
#print axioms whole_norm_coercivity_and_absolute_bound
#print axioms ordinary_minor_from_absolute_residuals
#print axioms whole_scaled_minor_decay_payment
#print axioms complete_four_corner_polynomial_budgets
#print axioms generic_corrected_tail_corner
#print axioms cumulative_negative_constant_improves_minor
#print axioms coupled_negative_constant_preserves_comparison
#print axioms whole_reference_tail_polynomial_identity
#print axioms source_constant_and_tail_mean
#print axioms cubic_reciprocal_root_rational_interval
#print axioms cumulative_log_concavity_entry_step
#print axioms exact_one_unit_cumulative_boundary_payment
#print axioms whole_nonnegative_three_step_recurrence
end InfiniteThreeFourReference
