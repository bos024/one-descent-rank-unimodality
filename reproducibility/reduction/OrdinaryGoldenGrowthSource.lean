import Mathlib
set_option maxRecDepth 4096

namespace OrdinaryGoldenGrowthSource

def ker (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => 1-q*ker q n

theorem kernel_box (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (heq : q^2+q=1) (n : ℕ) : q^2 ≤ ker q n ∧ ker q n ≤ 1 := by
  induction n with
  | zero => simp only [ker]; constructor <;> nlinarith
  | succ n ih => simp only [ker]; constructor <;> nlinarith [sq_nonneg q]

theorem signed_power_box (q : ℝ) (hq : 0<q) (hq1 : q<1) (n : ℕ) :
    -(q^3) ≤ (-q)^(n+3) ∧ (-q)^(n+3) ≤ q^3 := by
  induction n with
  | zero => norm_num; constructor <;> nlinarith [pow_nonneg (le_of_lt hq) 3]
  | succ n ih =>
      have hp : (-q)^(n+1+3)=(-q)^(n+3)*(-q) := by
        rw [show n+1+3=(n+3)+1 by omega, pow_succ]
      rw [hp]
      constructor <;> nlinarith [pow_nonneg (le_of_lt hq) 3]

theorem interval_spectral_factor (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (heq : q^2+q=1) (n : ℕ) :
    0 < q*(1-(-q)^(n+3)) ∧ q*(1-(-q)^(n+3)) ≤ 2*q^2 ∧ 2*q^2<1 := by
  obtain ⟨hl,hu⟩ := signed_power_box q hq hq1 n
  have hq2 : q^2<1 := by nlinarith
  have hq3 : q^3<1 := by nlinarith [mul_pos hq (sub_pos.mpr hq2)]
  have hq4 : q^4+q=2*q^2 := by nlinarith [sq_nonneg (q^2+q-1)]
  have hhalf : (1:ℝ)/2<q := by nlinarith [sq_nonneg (q-1/2)]
  constructor
  · exact mul_pos hq (sub_pos.mpr (lt_of_le_of_lt hu hq3))
  constructor
  · nlinarith [mul_nonneg (le_of_lt hq) (sub_nonneg.mpr hl)]
  · nlinarith

theorem finite_product_strict (v : List ℝ) (hne : v ≠ [])
    (hv : ∀ x ∈ v, 0<x ∧ x<1) : 0<v.prod ∧ v.prod<1 := by
  induction v with
  | nil => contradiction
  | cons x xs ih =>
      obtain ⟨hx0,hx1⟩ := hv x (by simp)
      by_cases hempty : xs=[]
      · subst xs; simpa using And.intro hx0 hx1
      · obtain ⟨hp0,hp1⟩ := ih hempty (by intro y hy; exact hv y (by simp [hy]))
        simp only [List.prod_cons]
        constructor
        · exact mul_pos hx0 hp0
        · nlinarith

theorem weighted_kernel_lower {ι : Type*} (S : Finset ι) (E K : ι → ℝ)
    (c : ℝ) (hE : ∀ i ∈ S, 0≤E i) (hK : ∀ i ∈ S, c≤K i) :
    c*(∑ i ∈ S, E i) ≤ ∑ i ∈ S, E i*K i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    c*E i = E i*c := mul_comm _ _
    _ ≤ E i*K i := mul_le_mul_of_nonneg_left (hK i hi) (hE i hi)

theorem convolution_current_atom (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (heq : q^2+q=1) (E : ℕ → ℝ) (hE : ∀ i, 0≤E i) (n : ℕ) :
    E n ≤ ∑ i ∈ Finset.range (n+1), E i*ker q (n-i) := by
  have hnon : ∀ i ∈ Finset.range (n+1), 0 ≤ E i*ker q (n-i) := by
    intro i hi
    exact mul_nonneg (hE i) (le_trans (sq_nonneg q) (kernel_box q hq hq1 heq (n-i)).1)
  have h := Finset.single_le_sum hnon (show n ∈ Finset.range (n+1) by simp)
  simpa [ker] using h

theorem positive_kernel_covers_mass (q M U : ℝ) (hq : 0<q)
    (heq : q^2+q=1) (hM : 3≤M) (hU : q^2*M≤U) : 1<U := by
  have hq1 : q<1 := by nlinarith [sq_nonneg q]
  have hupper : q<(2:ℝ)/3 := by nlinarith [sq_nonneg (q-2/3)]
  nlinarith

theorem golden_spectral_payment (U rho x : ℝ) (hU : 1≤U)
    (hrho0 : 0≤rho) (hrho1 : rho<1) (hx : x≤1) :
    0<U-rho*x := by nlinarith

theorem cumulative_density_step (a d : ℕ → ℝ) (n : ℕ)
    (hden : ∀ i ∈ Finset.range (n+1), d (n+1)*a i ≤ d i*a (n+1)) :
    (∑ i ∈ Finset.range (n+2), d i)*(∑ i ∈ Finset.range (n+1), a i) ≤
    (∑ i ∈ Finset.range (n+1), d i)*(∑ i ∈ Finset.range (n+2), a i) := by
  have hs : d (n+1)*(∑ i ∈ Finset.range (n+1), a i) ≤
      (∑ i ∈ Finset.range (n+1), d i)*a (n+1) := by
    simpa only [Finset.mul_sum, Finset.sum_mul] using Finset.sum_le_sum hden
  have ha : (∑ i ∈ Finset.range (n+2), a i) = (∑ i ∈ Finset.range (n+1), a i)+a (n+1) := Finset.sum_range_succ a (n+1)
  have hd : (∑ i ∈ Finset.range (n+2), d i) = (∑ i ∈ Finset.range (n+1), d i)+d (n+1) := Finset.sum_range_succ d (n+1)
  rw [ha,hd]
  nlinarith

theorem ordinary_density_golden_transfer (phi f0 f1 a0 a1 : ℝ)
    (ha0 : 0<a0) (hf0 : 0<f0) (hd : f1*a0≤f0*a1)
    (hg : a1<phi*a0) : f1<phi*f0 := by nlinarith

theorem actual_source_resource (q f0 f1 : ℝ) (heq : q^2+q=1)
    (hg : f1<(q+1)*f0) : q^2*f0<2*f0-f1 := by
  nlinarith [congrArg (fun x : ℝ => x*f0) heq]

theorem actual_source_increment_resource (q d0 d1 : ℝ) (heq : q^2+q=1)
    (hg : d1<(q+1)*d0) : q^2*d0<2*d0-d1 := by
  nlinarith [congrArg (fun x : ℝ => x*d0) heq]

#print axioms kernel_box
#print axioms signed_power_box
#print axioms interval_spectral_factor
#print axioms finite_product_strict
#print axioms weighted_kernel_lower
#print axioms convolution_current_atom
#print axioms positive_kernel_covers_mass
#print axioms golden_spectral_payment
#print axioms cumulative_density_step
#print axioms ordinary_density_golden_transfer
#print axioms actual_source_resource
#print axioms actual_source_increment_resource

end OrdinaryGoldenGrowthSource
