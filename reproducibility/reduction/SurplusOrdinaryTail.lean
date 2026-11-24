import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

namespace SurplusOrdinaryTail

theorem cumulative_head_bounds (q c w E2 J1 J2 B0 B1 : ℝ)
    (hqlo : 3/5 ≤ q) (hqhi : q ≤ 5/8) (heq : q^2+q=1)
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hw : 6 ≤ w)
    (hE2 : E2 ≤ w^2/2) (hJ1 : J1=w-q*(1-c))
    (hJ2 : J2=E2-q*J1) (hB0 : B0=1-q^2*c)
    (hB1 : B1=B0+J1) :
    0<B0 ∧ B0 ≤ 7/5 ∧ w ≤ B1 ∧ B1 ≤ w+1 ∧
    w-5/4 ≤ J1 ∧ J2 ≤ w^2/2 := by
  have hq2 : q^2 ≤ 2/5 := by nlinarith
  have hq0 : 0 ≤ q := by linarith
  have h1 := mul_nonneg (sq_nonneg q) (show 0 ≤ 1-c by linarith)
  have h2 := mul_nonneg (sq_nonneg q) (show 0 ≤ c+1 by linarith)
  have h3 := mul_nonneg (show 0 ≤ q-q^2 by nlinarith) (show 0 ≤ c+1 by linarith)
  have h4 := mul_nonneg (show 0 ≤ q-q^2 by nlinarith) (show 0 ≤ 1-c by linarith)
  have h5 := mul_nonneg hq0 (show 0 ≤ c+1 by linarith)
  have hJ1lo : w-5/4 ≤ J1 := by nlinarith
  have hJ10 : 0 ≤ J1 := by linarith
  have h6 := mul_nonneg hq0 hJ10
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  exact ⟨hJ1lo,by nlinarith⟩

theorem cumulative_quotient_seed (B0 B1 J1 J2 w : ℝ)
    (hw : 6 ≤ w) (hB00 : 0 ≤ B0) (hB0 : B0 ≤ 7/5)
    (hB1 : w ≤ B1) (hJ1 : w-5/4 ≤ J1) (hJ2 : J2 ≤ w^2/2) :
    0<B1*J1-B0*J2 := by
  have h10 : 0 ≤ J1 := by linarith
  have h1 := mul_nonneg (show 0 ≤ B1-w by linarith) h10
  have h2 := mul_nonneg (show 0 ≤ w by linarith) (show 0 ≤ J1-(w-5/4) by linarith)
  have h3 := mul_nonneg hB00 (show 0 ≤ w^2/2-J2 by linarith)
  have h4 := mul_nonneg (show 0 ≤ 7/5-B0 by linarith) (sq_nonneg w)
  have h5 := mul_nonneg (show 0 ≤ w-6 by linarith) (show 0 ≤ w by linarith)
  nlinarith

theorem cumulative_ratio_step (A B C p q r : ℝ)
    (hp : 0<p) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hAB : B=A+p) (hBC : C=B+q)
    (hseed : 0 ≤ B*p-A*q) (hlc : p*r ≤ q^2) :
    0 ≤ C*q-B*r := by
  have h1 := mul_nonneg hq hseed
  have h2 := mul_nonneg hB (show 0 ≤ q^2-p*r by linarith)
  have hid : p*(C*q-B*r)=q*(B*p-A*q)+B*(q^2-p*r) := by
    rw [hBC,hAB]
    ring
  nlinarith

theorem whole_cumulative_prefix_LC (B J : ℕ → ℝ) (K : ℕ)
    (hB : ∀ n,0 ≤ B n) (hJ : ∀ n,n ≤ K → 0<J n)
    (hs : ∀ n,B (n+1)=B n+J n)
    (hLC : ∀ n,n+2 ≤ K → J n*J (n+2) ≤ (J (n+1))^2)
    (hseed : 0 ≤ B 1*J 0-B 0*J 1) :
    ∀ n,n+1 ≤ K → B n*B (n+2) ≤ (B (n+1))^2 := by
  have hz : ∀ n,n+1 ≤ K → 0 ≤ B (n+1)*J n-B n*J (n+1) := by
    intro n
    induction n with
    | zero => intro hn; exact hseed
    | succ n ih =>
        intro hn
        exact cumulative_ratio_step (B n) (B (n+1)) (B (n+2))
          (J n) (J (n+1)) (J (n+2))
          (hJ n (by omega)) (le_of_lt (hJ (n+1) (by omega)))
          (hB (n+1)) (hs n) (hs (n+1)) (ih (by omega)) (hLC n (by omega))
  intro n hn
  have hh := hz n hn
  rw [hs n] at hh
  rw [hs (n+1),hs n]
  nlinarith

theorem cumulative_source_startup_budgets (w E2 p : ℝ)
    (hw : 6 ≤ w) (_hp0 : 0 ≤ p) (hp : p ≤ 13/8)
    (hlo : (w*(w-1))/2+1 ≤ E2) (hhi : E2 ≤ w^2/2) :
    2*p*(w+1)<E2+w+1 ∧ E2+w+1 ≤ (w+1)^2 := by
  have h1 := mul_nonneg (show 0 ≤ 13/8-p by linarith) (show 0 ≤ w+1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ w-6 by linarith) (show 0 ≤ 2*w+1 by linarith)
  constructor <;> nlinarith

theorem first_startup_payment (M X P p w : ℝ)
    (hM : 0 ≤ M) (hP : 0<P) (hX : X ≤ p*P)
    (hp : p ≤ 13/8) (hw : 6 ≤ w) :
    0<M-2*X+1+P*(w+1) := by
  have h1 := mul_nonneg (show 0 ≤ 13/8-p by linarith) (le_of_lt hP)
  have h2 := mul_nonneg (show 0 ≤ w-6 by linarith) (le_of_lt hP)
  nlinarith

theorem second_startup_payment (M X P Next p M1 M2 : ℝ)
    (hM : 0 ≤ M) (hP : 0<P) (hX : X ≤ p*P) (hNext : 0 ≤ Next)
    (hM1 : 0 ≤ M1) (hM2 : 2*p*M1<M2) (hbox : M2 ≤ M1^2) :
    0<M+P*M2-2*M1*X+Next+M1^2-M2 := by
  have h1 := mul_nonneg hM1 (show 0 ≤ p*P-X by linarith)
  have h2 := mul_pos hP (show 0<M2-2*p*M1 by linarith)
  nlinarith

theorem reference_amplitude_boundary_budget (x y A R : ℝ)
    (hx : 0<x) (hy : (3/2)*x ≤ y)
    (hA : A ≤ (117/50)*x) (hR : R=x+y) : A<R := by nlinarith

theorem first_missing_ordinary_boundary_payment (m A P delta : ℝ)
    (hm : -A ≤ m) (hA : A ≤ P) (hP : 0 ≤ P) (hd : 1 ≤ delta) :
    0 ≤ m+P*delta := by
  nlinarith [mul_nonneg hP (show 0 ≤ delta-1 by linarith)]

theorem constant_reference_density_excludes_strict_growth (F G I : ℝ)
    (hI : 0<I) (hdensity : G*I ≤ F*I) : G ≤ F := by nlinarith

#print axioms cumulative_head_bounds
#print axioms cumulative_quotient_seed
#print axioms cumulative_ratio_step
#print axioms whole_cumulative_prefix_LC
#print axioms cumulative_source_startup_budgets
#print axioms first_startup_payment
#print axioms second_startup_payment
#print axioms reference_amplitude_boundary_budget
#print axioms first_missing_ordinary_boundary_payment
#print axioms constant_reference_density_excludes_strict_growth

end SurplusOrdinaryTail

