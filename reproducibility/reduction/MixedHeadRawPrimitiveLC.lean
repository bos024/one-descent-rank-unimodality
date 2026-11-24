import Mathlib
namespace MixedHeadRawPrimitiveLC

theorem direct_raw_source_kernel (lam q d dn d0 : ℝ)
    (hsum : lam * q ≤ dn - d0)
    (hstep : lam * d ≤ dn - d) :
    lam * (q + d) + d0 ≤ 2 * dn - d := by
  nlinarith

theorem arbitrary_ordinary_opposite_transport {ι : Type*}
    (S : Finset ι) (b E H : ι → ℝ) (lam d0 boundary : ℝ)
    (hb : ∀ i ∈ S, 0 ≤ b i)
    (hpoint : ∀ i ∈ S, lam * E i + d0 ≤ H i)
    (hboundary : 0 ≤ boundary) :
    lam * (∑ i ∈ S, b i * E i) + d0 * (∑ i ∈ S, b i)
      ≤ (∑ i ∈ S, b i * H i) + boundary := by
  have hp : (∑ i ∈ S, b i * (lam * E i + d0)) ≤
      ∑ i ∈ S, b i * H i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hpoint i hi) (hb i hi)
  simp only [mul_add, Finset.sum_add_distrib] at hp
  have he : (∑ i ∈ S, b i * (lam * E i)) = lam * (∑ i ∈ S, b i * E i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hd : (∑ i ∈ S, b i * d0) = d0 * (∑ i ∈ S, b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,hd] at hp
  linarith

theorem strict_height_direct_payment (lam E tail d H T surplus : ℝ)
    (hlam : 0 < lam) (hheight : tail < E) (hd : d ≤ tail)
    (hT : T ≤ lam * d) (hsurplus : 0 ≤ surplus)
    (hhead : lam * E + surplus ≤ H) : T < H := by
  have hp : lam * d < lam * E := mul_lt_mul_of_pos_left (by linarith) hlam
  linarith

#print axioms direct_raw_source_kernel
#print axioms arbitrary_ordinary_opposite_transport
#print axioms strict_height_direct_payment
end MixedHeadRawPrimitiveLC
