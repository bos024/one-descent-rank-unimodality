import Mathlib
set_option maxHeartbeats 3000000
namespace ParameterizedRenewalResidual

theorem complete_parameter_boundary_identities (p θ : ℝ) :
    p^2-(p/2)*(2*p-1)=p/2 ∧
    (2*p-1)^2-p*(4*p-3+θ)=1-(1+θ)*p ∧
    (4*p-3+θ)^2-(2*p-1)*(8*p-8+3*θ)=θ*(2*p-1)+(θ-1)^2 := by
  constructor
  · ring
  · constructor <;> ring

theorem complete_parameter_boundary_bounds (p θ C : ℝ)
    (hp : 1/2<p) (hθ : 1≤θ) (hC : θ+1≤C)
    (hlast : θ+(θ-1)^2/(2*p-1)≤C) :
    -C*(p/2)≤p/2 ∧ p/2≤C*(p/2) ∧
    -C*p≤1-(1+θ)*p ∧ 1-(1+θ)*p≤C*p ∧
    -C*(2*p-1)≤θ*(2*p-1)+(θ-1)^2 ∧
    θ*(2*p-1)+(θ-1)^2≤C*(2*p-1) := by
  have hb : 0<2*p-1 := by linarith
  have hp0 : 0<p := by linarith
  have hC0 : 0≤C := by linarith
  have hlast' : θ*(2*p-1)+(θ-1)^2≤C*(2*p-1) := by
    have h := (div_le_iff₀ hb).mp (show (θ-1)^2/(2*p-1)≤C-θ by linarith)
    nlinarith only [h]
  have hmiddle : (1+θ)*p≤C*p := mul_le_mul_of_nonneg_right (by linarith) hp0.le
  have hbig : 1≤(1+θ)*p+C*p := by
    have hprod := mul_nonneg (show 0≤θ-1 by linarith) hp0.le
    nlinarith only [hprod,hmiddle,hp]
  have hpos : 0≤θ*(2*p-1)+(θ-1)^2 := by positivity
  have hCp : 0≤C*p := mul_nonneg hC0 hp0.le
  have hCb : 0≤C*(2*p-1) := mul_nonneg hC0 hb.le
  constructor
  · nlinarith only [hCp,hp0]
  · constructor
    · have h := mul_nonneg (show 0≤C-1 by linarith) hp0.le
      nlinarith only [h]
    · constructor
      · linarith
      · constructor
        · linarith
        · exact ⟨by linarith,hlast'⟩

theorem complete_parameter_probability_lower_band (d p θ C : ℝ)
    (hd : 0<d) (hd1 : d<1) (_hp : 0<p) (hdp : d*p<1)
    (hθ : 1≤θ) (hC : θ+1≤C) :
    -C< -(θ+1)+2*d-d^2*p ∧
    -C<θ-2*d*(θ-1)-d^2*(2*p-1) ∧
    ∀ H : ℝ,0≤H → H≤p → -C< -d^2*H ∧ -C<1-d^2*H := by
  have hdp2 : d^2*p<d := by nlinarith only [hd,hdp]
  have hfirst : -(θ+1)< -(θ+1)+2*d-d^2*p := by nlinarith only [hdp2,hd]
  have hmid : θ-2*d*θ+d^2<θ-2*d*(θ-1)-d^2*(2*p-1) := by
    nlinarith only [hdp2]
  have hh : 0≤(1-d)*(2*θ-1-d) := mul_nonneg (by linarith) (by linarith)
  have hlow : 1-θ≤θ-2*d*θ+d^2 := by nlinarith only [hh]
  refine ⟨by linarith,by linarith,?_⟩
  intro H _hH hHp
  have hhH := mul_le_mul_of_nonneg_left hHp (sq_nonneg d)
  constructor <;> nlinarith only [hhH,hdp2,hd1,hθ,hC]

theorem adjacent_root_power_entrance (m : ℕ) (θ d : ℝ)
    (hm : 1 ≤ m) (hθ : 1 < θ) (hθ2 : θ < 2)
    (hd : 0 < d) (hroot : d*θ^m = 1) : 1 < d*2^m := by
  have hp : θ^m < (2:ℝ)^m := by gcongr
  have h := mul_lt_mul_of_pos_left hp hd
  linarith

theorem uniform_parameter_constant_arithmetic (θ b : ℝ)
    (hθ : 1≤θ) (hroot : θ^2+2*θ≤6)
    (hb : 7-4*θ≤b) :
    0<b ∧ (θ-1)^2/b≤1 := by
  have hbound : (θ-1)^2≤b := by nlinarith only [hroot,hb]
  have hpos : 0<b := by
    by_cases h : θ=1
    · subst θ; linarith
    · have : 0<(θ-1)^2 := sq_pos_of_ne_zero (by intro he; apply h; linarith)
      linarith
  exact ⟨hpos,(div_le_one hpos).mpr hbound⟩

theorem all_delay_finite_polynomial_identity (R : Type*) [CommRing R]
    (l z : R) (m : ℕ) :
    (1-l*z)*(1+(l-2)*z+(l-1)^2*z^2*
      (∑ j ∈ Finset.range m,(l*z)^j))=
      (1-z)^2-l^m*(l-1)^2*z^(m+2) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (1-l*z)*(1+(l-2)*z+(l-1)^2*z^2*
          (∑ j ∈ Finset.range m,(l*z)^j))+
          (1-l*z)*(l-1)^2*z^2*(l*z)^m := by ring
      _ = _ := by rw [ih,mul_pow,pow_succ]; ring

theorem all_delay_positive_forcing_mass (l : ℝ) (m : ℕ) :
    l-1+(l-1)^2*(∑ j ∈ Finset.range m,l^j)=(l-1)*l^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,mul_add,← add_assoc,ih,pow_succ]
    ring

theorem positive_finite_convolution_two_sided (N U B : ℕ → ℝ)
    (n t : ℕ) (M : ℝ)
    (hN : ∀ i,0≤N i) (hB : ∀ j,0≤B j)
    (hU : ∀ k,0≤U k ∧ U k≤1)
    (hmass : ∑ j ∈ Finset.range t,B j≤M) :
    N n≤N n+∑ i ∈ Finset.range (n+1),
      N i*(∑ j ∈ Finset.range t,if j+2≤n-i then B j*U (n-i-(j+2)) else 0) ∧
    N n+∑ i ∈ Finset.range (n+1),
      N i*(∑ j ∈ Finset.range t,if j+2≤n-i then B j*U (n-i-(j+2)) else 0)
      ≤N n+M*(∑ i ∈ Finset.range (n+1),if i+2≤n then N i else 0) := by
  have inner : ∀ i,0≤(∑ j ∈ Finset.range t,
      if j+2≤n-i then B j*U (n-i-(j+2)) else 0) ∧
      (∑ j ∈ Finset.range t,if j+2≤n-i then B j*U (n-i-(j+2)) else 0)
      ≤ (if i+2≤n then M else 0) := by
    intro i
    have hn : 0≤∑ j ∈ Finset.range t,
        if j+2≤n-i then B j*U (n-i-(j+2)) else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact mul_nonneg (hB j) (hU _).1
      · rfl
    refine ⟨hn,?_⟩
    by_cases hi : i+2≤n
    · simp only [hi,ite_true]
      apply le_trans _ hmass
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact mul_le_of_le_one_right (hB j) (hU _).2
      · exact hB j
    · simp only [hi,ite_false]
      have hz : ∀ j,¬j+2≤n-i := by intro j hj; omega
      simp [hz]
  constructor
  · have h := Finset.sum_nonneg (s:=Finset.range (n+1))
      (f:=fun i => N i*(∑ j ∈ Finset.range t,
        if j+2≤n-i then B j*U (n-i-(j+2)) else 0))
      (fun i _ => mul_nonneg (hN i) (inner i).1)
    linarith
  · apply add_le_add le_rfl
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1),N i*(if i+2≤n then M else 0) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (inner i).2 (hN i)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring

theorem whole_arbitrary_tail_numerator_recursion
    (R : Type*) [CommRing R] (P S N : R) :
    P+S*N=1+(P+S-1)+S*(N-1) := by ring

#print axioms complete_parameter_boundary_identities
#print axioms complete_parameter_boundary_bounds
#print axioms complete_parameter_probability_lower_band
#print axioms adjacent_root_power_entrance
#print axioms uniform_parameter_constant_arithmetic
#print axioms all_delay_finite_polynomial_identity
#print axioms all_delay_positive_forcing_mass
#print axioms positive_finite_convolution_two_sided
#print axioms whole_arbitrary_tail_numerator_recursion
end ParameterizedRenewalResidual
