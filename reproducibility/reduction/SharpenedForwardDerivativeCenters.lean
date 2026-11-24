import Mathlib

set_option maxHeartbeats 0
noncomputable section
namespace SharpenedForwardDerivativeCenters

def interval {R : Type*} [CommRing R] (z : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, z ^ i

theorem interval_mul_complement {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    interval z n * (1-z) = 1-z^n := by
  exact geom_sum_mul_neg z n

theorem two_source_positive_decomposition {R : Type*} [CommRing R] [IsDomain R]
    (z : R) (a g : ℕ) :
    interval z (a+g) + z*interval z (a+g+1)*interval z a =
      interval z a*interval z (a+g+2) + z^a*interval z g := by
  by_cases hz : z=1
  · subst z
    simp only [interval,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,one_mul]
    push_cast
    ring
  · have hc : (1-z)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hz))
    apply mul_right_cancel₀ hc
    calc
      (interval z (a+g)+z*interval z (a+g+1)*interval z a)*(1-z)^2 =
          (interval z (a+g)*(1-z))*(1-z)+
            z*(interval z (a+g+1)*(1-z))*(interval z a*(1-z)) := by ring
      _ = (1-z^(a+g))*(1-z)+z*(1-z^(a+g+1))*(1-z^a) := by
        rw [interval_mul_complement,interval_mul_complement,interval_mul_complement]
      _ = (1-z^a)*(1-z^(a+g+2))+z^a*(1-z^g)*(1-z) := by
        simp only [pow_add,pow_succ]
        ring
      _ = (interval z a*interval z (a+g+2)+z^a*interval z g)*(1-z)^2 := by
        rw [← interval_mul_complement z a,← interval_mul_complement z (a+g+2),
          ← interval_mul_complement z g]
        ring

theorem base_component_centers (a b : ℤ) :
    (a-2)+b=a+b-2 ∧ 2*(a-1)+(b-a-1)=a+b-3 := by constructor <;> ring

theorem arbitrary_tail_center_induction (W h t : ℤ) (hsize : 1 ≤ W+h) :
    (W+h-4)+(t+1)=(W+t)+(h+1)-4 ∧
      t-2 ≤ (W+t)+(h+1)-4 := by constructor <;> omega

theorem later_finite_correction_center (α W h : ℤ) :
    (2*(α+h-1)+(W-h))-(W+h-4)=2*α+2 := by ring

theorem sharpened_shifted_mode_bound (j W h : ℕ)
    (hsize : 4 ≤ W+h) (hmode : 2*j ≤ W+h-4) :
    j+2 ≤ (W+h)/2 := by omega

theorem equal_first_pair_boundary_last_gap (a v u n : ℤ)
    (hn : n=2*a+v+3) (hcenter : 2*n ≤ 4*a+2*v+u+4) :
    2 ≤ u := by omega

#print axioms two_source_positive_decomposition
#print axioms base_component_centers
#print axioms arbitrary_tail_center_induction
#print axioms later_finite_correction_center
#print axioms sharpened_shifted_mode_bound
#print axioms equal_first_pair_boundary_last_gap

end SharpenedForwardDerivativeCenters
