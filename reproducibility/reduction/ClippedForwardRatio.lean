import Mathlib

set_option maxHeartbeats 0
namespace ClippedForwardRatio

theorem raw_deficit_identity {R : Type*} [CommRing R]
    (z A B E : R) (hE : E=1-z+(2*z-1)*B) :
    (2*z-1)*A*B=E*A-(1-z)*A := by
  rw [hE]
  ring

theorem clipped_threshold (H0 H1 d0 d1 : ℤ)
    (hd0 : 0 < d0) (hd1 : 0 < d1)
    (hratio : min H0 d0*d1 ≤ min H1 d1*d0)
    (hcross : d0 ≤ H0) : d1 ≤ H1 := by
  rw [min_eq_right hcross] at hratio
  have hh := min_le_left H1 d1
  have hp := mul_le_mul_of_nonneg_right hh (le_of_lt hd0)
  by_contra hfail
  have hstrict := mul_neg_of_neg_of_pos (by omega : H1-d1 < 0) hd0
  nlinarith

theorem weighted_sum_growth {ι : Type*} (s : Finset ι)
    (A B0 B1 : ι → ℤ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (hg : ∀ i ∈ s, B1 i ≤ 2*B0 i) :
    (∑ i ∈ s, A i*B1 i) ≤ 2*(∑ i ∈ s, A i*B0 i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (hg i hi) (hA i hi)
  nlinarith

theorem short_factor_index (a n i : ℕ) (hn : a < n) (hi : i ≤ a) :
    1 ≤ n-i ∧ n-i-1=n-1-i := by omega

theorem two_losses (wprev w wnext u v unext vnext : ℤ)
    (hdrop : wprev-w=u+v) (hnext : w-wnext=unext+vnext)
    (hfall : 2*w < wprev)
    (hloss : u+v ≤ 2*(unext+vnext)) : 2*wnext < w := by
  omega

theorem weighted_ratio_sum {ι : Type*} (s : Finset ι)
    (w G0 G1 : ι → ℤ) (d0 d1 : ℤ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hG : ∀ i ∈ s, G0 i*d1 ≤ G1 i*d0) :
    (∑ i ∈ s, w i*G0 i)*d1 ≤
      (∑ i ∈ s, w i*G1 i)*d0 := by
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (hG i hi) (hw i hi)
  nlinarith

theorem complement_threshold (H d Q : ℤ) (hid : Q=H-d)
    (hQ : 0 ≤ Q) : d ≤ H := by omega

theorem prefix_budget_transfer {ι : Type*} (s : Finset ι)
    (d G : ι → ℤ) (dN GN base : ℤ)
    (hbase : dN ≤ base*GN)
    (hp : ∀ i ∈ s, dN*G i ≤ d i*GN) :
    dN*(1+∑ i ∈ s, G i) ≤ (base+∑ i ∈ s, d i)*GN := by
  have hs := Finset.sum_le_sum hp
  rw [← Finset.mul_sum,← Finset.sum_mul] at hs
  nlinarith

#print axioms raw_deficit_identity
#print axioms clipped_threshold
#print axioms weighted_sum_growth
#print axioms short_factor_index
#print axioms two_losses
#print axioms weighted_ratio_sum
#print axioms complement_threshold
#print axioms prefix_budget_transfer
end ClippedForwardRatio
