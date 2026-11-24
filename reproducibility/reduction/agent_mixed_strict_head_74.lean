import Mathlib

namespace AgentMixedStrictHead74

def headBound (K : ℤ) : ℤ := (37*K-111)/2
def mainDegreeFloor (K : ℤ) : ℤ := 1+(K-2)*(K-1)/2
def otherDegreeFloor (K : ℤ) : ℤ := 1+(K-3)*(K-2)/2

theorem source_birth_gap_forces_reverse_rank (D r d e : ℤ)
    (hD : D=2*r+e+2) (he : e ≤ d-3) : D-d+1 ≤ 2*r := by omega

theorem positive_recovery_forward_rank_bound (K alpha D h r j : ℤ)
    (ha : 1 ≤ alpha) (hh : h ≤ D)
    (hD : D ≤ 12*(K-alpha)-25)
    (hr : D-(K-alpha)+1 ≤ 2*r)
    (hj : j=alpha+D+h-r) : 2*j ≤ 37*K-111 := by omega

theorem proper_head_bound (K j k : ℤ)
    (hj : 2*j ≤ 37*K-111) (hk : k < j) : k+1 ≤ headBound K := by
  unfold headBound
  omega

theorem second_window_keeps_raw_source_prefix (a b j n k : ℤ)
    (hj : j=a+b-n) (hsecond : k+n+2<a+b)
    (hja : j ≤ a+1) : k+1 ≤ a-1 := by omega

theorem unit_recovery_head_bound (K a j k : ℤ)
    (hK : 74 ≤ K) (ha : a ≤ K-3) (hj : j=a+1) (hk : k < j) :
    k+1 ≤ headBound K := by
  unfold headBound
  omega

theorem uniform_74_main_box_budget (K : ℤ) (hK : 74 ≤ K) :
    2*headBound K ≤ mainDegreeFloor K ∧
    headBound K ≤ otherDegreeFloor K := by
  let N := headBound K
  have hN : 2*N ≤ 37*K-111 := by dsimp [N,headBound]; omega
  have hpoly := mul_nonneg (show 0 ≤ K-74 by omega) (show 0 ≤ K-3 by omega)
  have hpoly2 := mul_nonneg (show 0 ≤ K-74 by omega) (show 0 ≤ K+32 by omega)
  have hp1 : 4*N-2 ≤ (K-2)*(K-1) := by nlinarith
  have hp2 : 2*N-2 ≤ (K-3)*(K-2) := by nlinarith
  change 2*N ≤ 1+(K-2)*(K-1)/2 ∧ N ≤ 1+(K-3)*(K-2)/2
  omega

theorem actual_main_box_support_covers_head (M B N Mmin Othermin : ℤ)
    (hM : Mmin ≤ M) (hOther : Othermin ≤ M-B)
    (hN : 2*N ≤ Mmin) (hNOther : N ≤ Othermin) :
    N ≤ min (M/2) (M-B) := by omega

theorem one_nonnegative_convolution_term_pays {ι : Type*}
    (S : Finset ι) (A B : ι → ℝ) (i0 : ι) (C : ℝ)
    (hi0 : i0 ∈ S) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hB : ∀ i ∈ S, 0 ≤ B i) (_hC : 0 ≤ C)
    (hterm : C ≤ A i0) (hunit : 1 ≤ B i0) :
    C ≤ ∑ i ∈ S, A i*B i := by
  have hprod : C ≤ A i0*B i0 := by
    have hm := mul_nonneg (hA i0 hi0) (show 0 ≤ B i0-1 by linarith)
    nlinarith
  have hs : A i0*B i0 ≤ ∑ i ∈ S, A i*B i := by
    exact Finset.single_le_sum (fun i hi => mul_nonneg (hA i hi) (hB i hi)) hi0
  exact le_trans hprod hs

theorem raw_owner_source_dominates_curvature (qcur qnext d dnext C raw : ℝ)
    (hq : 0 ≤ qnext) (hd : 0 ≤ d)
    (hnext : qnext=qcur+dnext) (hC : C=dnext-d)
    (hraw : raw=2*qnext-qcur) : C ≤ raw := by nlinarith

#print axioms source_birth_gap_forces_reverse_rank
#print axioms positive_recovery_forward_rank_bound
#print axioms proper_head_bound
#print axioms second_window_keeps_raw_source_prefix
#print axioms unit_recovery_head_bound
#print axioms uniform_74_main_box_budget
#print axioms actual_main_box_support_covers_head
#print axioms one_nonnegative_convolution_term_pays
#print axioms raw_owner_source_dominates_curvature

end AgentMixedStrictHead74
