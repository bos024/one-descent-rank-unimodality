import Mathlib
set_option maxHeartbeats 3000000
namespace ProbabilityQuadraticMinorEnvelope

theorem quadratic_perspective_criterion (H e C w : ℝ) (hH : 0<H) :
    (∀ x : ℝ,0 ≤ H*x^2-2*e*x+C-w) ↔ e^2+H*w ≤ C*H := by
  constructor
  · intro h
    have h0 := h (e/H)
    have hid : H*(e/H)^2-2*e*(e/H)+C-w=(C*H-e^2-H*w)/H := by
      field_simp
      ring
    rw [hid] at h0
    have hh := mul_nonneg h0 (le_of_lt hH)
    rw [div_mul_cancel₀ _ (ne_of_gt hH)] at hh
    linarith
  · intro h x
    have hh : 0 ≤ H*(H*x^2-2*e*x+C-w) := by
      nlinarith only [h,sq_nonneg (H*x-e)]
    nlinarith only [hh,hH]

theorem finite_probability_quadratic_transport (t : ℕ) (a Hs es ws : ℕ → ℝ)
    (H e C w : ℝ) (ha : ∀ i,i<t → 0 ≤ a i)
    (hmass : ∑ i ∈ Finset.range t,a i=1)
    (hH : ∑ i ∈ Finset.range t,a i*Hs i ≤ H)
    (he : ∑ i ∈ Finset.range t,a i*es i=e)
    (hw : ∑ i ∈ Finset.range t,a i*ws i=w)
    (hQ : ∀ i,i<t → ∀ x : ℝ,0 ≤ Hs i*x^2-2*es i*x+C-ws i) :
    ∀ x : ℝ,0 ≤ H*x^2-2*e*x+C-w := by
  intro x
  have hs : 0 ≤ ∑ i ∈ Finset.range t,a i*(Hs i*x^2-2*es i*x+C-ws i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i (Finset.mem_range.mp hi)) (hQ i (Finset.mem_range.mp hi) x)
  have hid : (∑ i ∈ Finset.range t,a i*(Hs i*x^2-2*es i*x+C-ws i))=
      (∑ i ∈ Finset.range t,a i*Hs i)*x^2-2*e*x+C-w := by
    calc
      _ = ∑ i ∈ Finset.range t,
          (x^2*(a i*Hs i)-(2*x)*(a i*es i)+C*a i-a i*ws i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by
            simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
            rw [hmass,he,hw]
            ring
  rw [hid] at hs
  have hh := mul_nonneg (show 0 ≤ H-(∑ i ∈ Finset.range t,a i*Hs i) by linarith) (sq_nonneg x)
  nlinarith only [hs,hh]

theorem whole_probability_quadratic_invariant (t : ℕ) (a H e w : ℕ → ℝ) (C : ℝ)
    (_ht : 1 ≤ t) (ha : ∀ i,i<t → 0 ≤ a i)
    (hmass : ∑ i ∈ Finset.range t,a i=1)
    (he : ∀ n,t ≤ n → e n=∑ i ∈ Finset.range t,a i*e (n-(i+1)))
    (hw : ∀ n,t ≤ n → w n=∑ i ∈ Finset.range t,a i*w (n-(i+1)))
    (hH : ∀ n,t ≤ n → (∑ i ∈ Finset.range t,a i*H (n-(i+1))) ≤ H n)
    (hbase : ∀ n,n<t → -C ≤ w n ∧ ∀ x : ℝ,0 ≤ H n*x^2-2*e n*x+C-w n) :
    ∀ n,-C ≤ w n ∧ ∀ x : ℝ,0 ≤ H n*x^2-2*e n*x+C-w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<t
    · exact hbase n hn
    · have hge : t ≤ n := by omega
      have hprev : ∀ i,i<t → -C ≤ w (n-(i+1)) ∧
          ∀ x : ℝ,0 ≤ H (n-(i+1))*x^2-2*e (n-(i+1))*x+C-w (n-(i+1)) := by
        intro i hi
        exact ih (n-(i+1)) (by omega)
      constructor
      · have hs : 0 ≤ ∑ i ∈ Finset.range t,a i*(w (n-(i+1))+C) := by
          apply Finset.sum_nonneg
          intro i hi
          have h := (hprev i (Finset.mem_range.mp hi)).1
          exact mul_nonneg (ha i (Finset.mem_range.mp hi)) (by linarith)
        simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul] at hs
        rw [hmass,← hw n hge] at hs
        linarith
      · apply finite_probability_quadratic_transport t a
          (fun i => H (n-(i+1))) (fun i => e (n-(i+1)))
          (fun i => w (n-(i+1))) (H n) (e n) C (w n)
          ha hmass (hH n hge) (he n hge).symm (hw n hge).symm
        intro i hi
        exact (hprev i hi).2

theorem exact_minor_renewal_perspective_and_bounds (H f g l C : ℝ)
    (hH : 0<H)
    (hw : -C ≤ l*(f-l*H)-(g-l*f))
    (hQ : ∀ x : ℝ,0 ≤ H*x^2-2*(f-l*H)*x+C-(l*(f-l*H)-(g-l*f))) :
    -C*H ≤ f^2-H*g ∧ f^2-H*g ≤ C*H := by
  have hid : f^2-H*g=(f-l*H)^2+H*(l*(f-l*H)-(g-l*f)) := by ring
  have hu := (quadratic_perspective_criterion H (f-l*H) C
    (l*(f-l*H)-(g-l*f)) hH).mp hQ
  have hl := mul_nonneg (le_of_lt hH) (show 0 ≤ l*(f-l*H)-(g-l*f)+C by linarith)
  constructor
  · nlinarith only [hl,sq_nonneg (f-l*H)]
  · rw [hid]
    exact hu

theorem all_order_geometric_and_first_two_boundary_minors (P q : ℝ) :
    (2*P)^2-P*(4*P)=0 ∧
    (2*P)^2-P*(4*P-1)=P ∧
    (4*P-1)^2-(2*P)*(8*P-3)=1-2*P ∧
    (2*P-1)^2-P*(4*P-2+q)=1-(2+q)*P ∧
    (2*P+q)^2-P*(4*P+2*q-(1-q))=(1+q)*P+q^2 := by
  constructor
  · ring
  · constructor
    · ring
    · constructor
      · ring
      · constructor <;> ring

#print axioms quadratic_perspective_criterion
#print axioms finite_probability_quadratic_transport
#print axioms whole_probability_quadratic_invariant
#print axioms exact_minor_renewal_perspective_and_bounds
#print axioms all_order_geometric_and_first_two_boundary_minors
end ProbabilityQuadraticMinorEnvelope
