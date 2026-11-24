import Mathlib

set_option maxHeartbeats 0
namespace OrdinaryRelativeGrowth

theorem window_ratio_transport {ι : Type*} (s : Finset ι) (p q : ι → ℤ)
    (pi po qi qo : ℤ)
    (hin : ∀ i ∈ s, pi*q i ≤ p i*qi)
    (hout : ∀ i ∈ s, p i*qo ≤ po*q i) :
    ((∑ i ∈ s, p i)+pi-po)*(∑ i ∈ s, q i) ≤
      (∑ i ∈ s, p i)*((∑ i ∈ s, q i)+qi-qo) := by
  have hi : pi*(∑ i ∈ s, q i) ≤ (∑ i ∈ s, p i)*qi := by
    rw [Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_le_sum hin
  have ho : (∑ i ∈ s, p i)*qo ≤ po*(∑ i ∈ s, q i) := by
    rw [Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_le_sum hout
  nlinarith

theorem clipped_ratio (a0 a1 b0 b1 : ℤ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1)
    (horder : b0*a1 ≤ b1*a0) :
    max (a1-b1) 0*a0 ≤ max (a0-b0) 0*a1 := by
  by_cases h1 : a1-b1 ≤ 0
  · rw [max_eq_right h1]
    exact le_of_eq_of_le (by ring) (mul_nonneg (le_max_right _ _) ha1)
  · rw [max_eq_left (by omega : 0 ≤ a1-b1)]
    by_cases h0 : a0-b0 ≤ 0
    · rw [max_eq_right h0]
      nlinarith [mul_nonneg (by omega : 0 ≤ b0-a0) ha1]
    · rw [max_eq_left (by omega : 0 ≤ a0-b0)]
      nlinarith

theorem ratio_transitivity (a0 a1 b0 b1 c0 c1 : ℤ)
    (ha0 : 0 ≤ a0) (hb0 : 0 ≤ b0) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hab : a1 ≤ b1)
    (h1 : a1*b0 ≤ a0*b1) (h2 : b1*c0 ≤ b0*c1) :
    a1*c0 ≤ a0*c1 := by
  by_cases hb : b0=0
  · subst b0
    nlinarith [mul_nonneg (by omega : 0 ≤ b1-a1) hc0,mul_nonneg ha0 hc1]
  · have hbpos : 0 < b0 := by omega
    have hh1 := mul_le_mul_of_nonneg_right h1 hc0
    have hh2 := mul_le_mul_of_nonneg_left h2 ha0
    have h : (a1*c0)*b0 ≤ (a0*c1)*b0 := by nlinarith
    exact (mul_le_mul_iff_left₀ hbpos).mp h

theorem curvature_resource (u0 u1 K0 K1 : ℤ)
    (hu : 0 ≤ u0) (hbound : u0 ≤ K0) (hK : 0 < K0)
    (hratio : u1*K0 ≤ u0*K1) (hcurv : u0<u1) :
    u1-u0 ≤ K1-K0 := by
  have hg : 0 ≤ K1-K0 := by
    by_contra hh
    nlinarith [mul_nonneg hu (le_of_lt (by omega : 0<K0-K1))]
  have hp := mul_le_mul_of_nonneg_right hbound hg
  by_contra hfail
  have hpos : 0 < u1-u0-(K1-K0) := by omega
  have hprod := mul_pos hpos hK
  nlinarith

#print axioms window_ratio_transport
#print axioms clipped_ratio
#print axioms ratio_transitivity
#print axioms curvature_resource
end OrdinaryRelativeGrowth
