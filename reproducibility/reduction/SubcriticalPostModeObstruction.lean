import Mathlib
import FastListPolynomial

set_option maxHeartbeats 0
namespace SubcriticalPostModeObstruction

def R : List ℤ := [1,5,14,28,43,53,53,43,28,14,5,1]
def coeff (i : ℕ) : ℤ := R[i]?.getD 0
def indicator (beta n : ℤ) : ℤ := if 0 ≤ n ∧ n ≤ beta then 1 else 0
def spline (beta n : ℤ) : ℤ :=
  ∑ i ∈ Finset.range 12, coeff i*indicator beta (n-(i:ℤ))

theorem exact_factor_product :
    FastListPolynomial.mul [1,1]
      (FastListPolynomial.mul [1,1,1]
        (FastListPolynomial.mul [1,1,1]
          (FastListPolynomial.mul [1,1,1,1] [1,1,1,1])))=R := by decide +kernel

theorem exact_weight_sum : (∑i∈Finset.range 12,coeff i)=288 := by decide +kernel

theorem plateau (beta n : ℤ) (hn : 11 ≤ n ∧ n ≤ beta) : spline beta n=288 := by
  unfold spline
  calc
    _ = ∑i∈Finset.range 12,coeff i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i<12 := Finset.mem_range.mp hi
      have hl : 0 ≤ n-(i:ℤ) := by omega
      have hni : (i:ℤ) ≤ n := by omega
      have hr : n-(i:ℤ) ≤ beta := by omega
      simp [indicator,hni,hr]
    _ = 288 := exact_weight_sum

theorem first_endpoint_loss (beta : ℤ) (hb : 11 ≤ beta) : spline beta (beta+1)=287 := by
  unfold spline
  calc
    _ = ∑i∈Finset.range 12,coeff i*(if i=0 then 0 else 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i<12 := Finset.mem_range.mp hi
      by_cases hz : i=0
      · subst i
        have hn : ¬beta+1 ≤ beta := by omega
        simp [indicator,hn]
      · have hl : 0 ≤ beta+1-(i:ℤ) := by omega
        have hni : (i:ℤ) ≤ beta+1 := by omega
        have hr : beta+1-(i:ℤ) ≤ beta := by omega
        simp [indicator,hni,hr,hz]
    _ = 287 := by decide +kernel

theorem initial_coefficients (beta : ℤ) (hb : 11 ≤ beta) :
    spline beta 0=1 ∧ spline beta 1=6 ∧ spline beta 2=20 ∧ spline beta 3=48 := by
  have h0 : 0 ≤ beta := by omega
  have h1 : 1 ≤ beta := by omega
  have h2 : 2 ≤ beta := by omega
  have h3 : 3 ≤ beta := by omega
  norm_num [spline,coeff,R,Finset.sum_range_succ,indicator,h0,h1,h2,h3] <;>
    split_ifs <;> omega

theorem one_sample_loss (D : ℕ) (e : ℕ → ℤ) (P : ℤ) :
    (∑i∈Finset.range (D+1),e i*(if i=0 then P-1 else P))=
      P*(∑i∈Finset.range (D+1),e i)-e 0 := by
  calc
    _ = ∑i∈Finset.range (D+1),(P*e i-if i=0 then e 0 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hz : i=0
      · simp [hz]
        ring
      · simp [hz,mul_comm]
    _ = _ := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum]
      simp

theorem parameter_domain (k c : ℤ) (hk : 20 ≤ k) (hc : 2*c=k*(k-1)) :
    18 ≤ k-2 ∧ k+18 ≤ c ∧ c+12-k ≤ c+2 ∧ 11 ≤ k+2 := by
  have hp : 0 ≤ (k-20)*(k+17) := mul_nonneg (by omega) (by omega)
  have ht : k+18 ≤ c := by nlinarith
  omega

theorem unbounded_gap_domain (k c L : ℤ)
    (hL : 4 ≤ L) (hk : L+16 ≤ k) (hc : 2*c=k*(k-1)) :
    L+14 ≤ k-2 ∧ k+L+14 ≤ c ∧ c+L+8-k ≤ c+2 ∧ L+7 ≤ k+2 := by
  have hk20 : 20 ≤ k := by omega
  have hp : 0 ≤ k*(k-5) := mul_nonneg (by omega) (by omega)
  have hc2 : 2*k ≤ c := by nlinarith
  omega

#print axioms exact_factor_product
#print axioms exact_weight_sum
#print axioms plateau
#print axioms first_endpoint_loss
#print axioms initial_coefficients
#print axioms one_sample_loss
#print axioms parameter_domain
#print axioms unbounded_gap_domain
end SubcriticalPostModeObstruction
