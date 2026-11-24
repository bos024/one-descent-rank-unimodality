import Mathlib

/- Scoped exact-window and scalar kernels. The actual source grammar,
   actual-mode identification, and unbounded coverage are in the written proof.
   The complete N6 closure is separately checked in SecondOffsetSourceCertificate. -/

namespace JointSourceGrowth

def window (w : ℤ → ℤ) (t n : ℤ) : ℤ :=
  ∑ i ∈ Finset.Icc (n-t) (n-1), w i

theorem two_window_terms (w : ℤ → ℤ) (t n i j : ℤ)
    (hi : n-t ≤ i ∧ i ≤ n-1) (hj : n-t ≤ j ∧ j ≤ n-1)
    (hne : i ≠ j) (hzero : ∀ r, r ≤ n-1 → 0 ≤ w r) :
    w i+w j ≤ window w t n := by
  have hs : ({i,j} : Finset ℤ) ⊆ Finset.Icc (n-t) (n-1) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_Icc.mpr hi
    · exact Finset.mem_Icc.mpr hj
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun r hr _ => hzero r (Finset.mem_Icc.mp hr).2)
  simpa [window, Finset.sum_pair hne] using h

theorem three_window_terms (w : ℤ → ℤ) (t n i j k : ℤ)
    (hi : n-t ≤ i ∧ i ≤ n-1) (hj : n-t ≤ j ∧ j ≤ n-1)
    (hk : n-t ≤ k ∧ k ≤ n-1)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzero : ∀ r, r ≤ n-1 → 0 ≤ w r) :
    w i+w j+w k ≤ window w t n := by
  have hs : ({i,j,k} : Finset ℤ) ⊆ Finset.Icc (n-t) (n-1) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact Finset.mem_Icc.mpr hi
    · exact Finset.mem_Icc.mpr hj
    · exact Finset.mem_Icc.mpr hk
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun r hr _ => hzero r (Finset.mem_Icc.mp hr).2)
  simpa [window, Finset.sum_insert, hij, hik, hjk, Finset.sum_pair, add_assoc] using h

theorem joint_pre_peak_window_payment (w : ℤ → ℤ) (kap t n ell d eta : ℤ)
    (hkap : 3 ≤ kap) (ht : kap-1 ≤ t) (heta : 1 ≤ eta)
    (hstart : (if t=kap-1 then kap+4 else kap+5) ≤ n)
    (hend : n-1 ≤ ell)
    (hzero : ∀ i, i ≤ ell → 0 ≤ w i)
    (hoffset : kap+2 ≤ ell → 1 ≤ w (kap+2))
    (htc : ∀ i, kap+3 ≤ i → i ≤ ell → d ≤ w i)
    (htcOne : ∀ i, kap+3 ≤ i → i ≤ ell → 1 ≤ w i)
    (hjoint : ∀ i, kap+4 ≤ i → i ≤ ell → d+eta ≤ w i) :
    (if t=kap-1 then d+1 else d+eta+d+(if t ≤ kap+1 then 1 else 0)) ≤
      window w t n+(if n=t+1 then 1 else 0)-(if n=t+2 then 1 else 0) := by
  have hz : ∀ i, i ≤ n-1 → 0 ≤ w i := fun i hi => hzero i (by omega)
  by_cases hstat : t=kap-1
  · simp only [ite_eq_left hstat] at hstart ⊢
    have hplus : n ≠ t+1 := by omega
    have hminus : n ≠ t+2 := by omega
    simp only [ite_eq_right hplus, ite_eq_right hminus, add_zero, sub_zero]
    by_cases hfirst : n=kap+4
    · have hs := two_window_terms w t n (kap+3) (kap+2) (by omega) (by omega) (by omega) hz
      have h1 := htc (kap+3) (by omega) (by omega)
      have h2 := hoffset (by omega)
      omega
    · have hi : n-t ≤ n-1 ∧ n-1 ≤ n-1 := by omega
      have hs : w (n-1) ≤ window w t n := by
        exact Finset.single_le_sum (fun i hi => hz i (Finset.mem_Icc.mp hi).2)
          (Finset.mem_Icc.mpr hi)
      have hj := hjoint (n-1) (by omega) hend
      omega
  · simp only [ite_eq_right hstat] at hstart ⊢
    have hthree := three_window_terms w t n (n-1) (n-2) (n-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz
    have h1 := hjoint (n-1) (by omega) hend
    have h2 := htc (n-2) (by omega) (by omega)
    have h3 : 1 ≤ w (n-3) := by
      by_cases heq : n=kap+5
      · have hid : n-3=kap+2 := by omega
        rw [hid]
        exact hoffset (by omega)
      · exact htcOne (n-3) (by omega) (by omega)
    by_cases hdent : n=t+2
    · have hfar : ¬t ≤ kap+1 := by omega
      have hplus : n ≠ t+1 := by omega
      simp only [ite_eq_right hfar, ite_eq_left hdent, ite_eq_right hplus]
      omega
    · simp only [ite_eq_right hdent]
      split_ifs <;> omega

theorem exponential_joint_budget : ∀ k : ℕ, 8 ≤ k →
    (k:ℤ)^2+7*(k:ℤ)+4 ≤ 2*(2:ℤ)^(k-2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hz : (8:ℤ) ≤ k := by exact_mod_cast hk
      have he : k+1-2=(k-2)+1 := by omega
      have hp : (2:ℤ)^(k+1-2)=2*(2:ℤ)^(k-2) := by
        rw [he, pow_succ]
        ring
      rw [hp]
      push_cast
      nlinarith [sq_nonneg (k:ℤ)]

theorem large_peak_pays_joint (k d M value J power : ℤ)
    (hd : d ≤ k) (hpeak : power-d ≤ M) (hvalue : M-1 ≤ value)
    (hexp : k*k+7*k+4 ≤ 2*power)
    (hjet : 2*J ≤ (k+1)*(k+4)-2) : J ≤ value := by nlinarith

theorem low_joint_peak_failure_region (n ell M J value : ℤ)
    (hheight : ell-2 ≤ M) (hpay : M+n-ell-3 ≤ value)
    (hpeak : M-1 ≤ value) (hJ : J ≤ 43) (hfail : value < J) :
    n ≤ 47 ∧ M ≤ 43 := by omega

theorem offset_linear_peak_payment (kap n ell M value : ℤ)
    (hkap : 3 ≤ kap) (hheight : ell-2 ≤ M)
    (hpay : M+n-ell-3 ≤ value) : n-kap-2 ≤ value := by omega

theorem linear_pre_peak_window_payment (w : ℤ → ℤ) (kap t n ell : ℤ)
    (hkap : 3 ≤ kap) (ht : kap-1 ≤ t)
    (hstart : (if t=kap-1 then kap+3 else kap+4) ≤ n)
    (hend : n-1 ≤ ell)
    (hzero : ∀ i, i ≤ ell → 0 ≤ w i)
    (hbirth : 1 ≤ w kap)
    (hoffset : kap+2 ≤ ell → 1 ≤ w (kap+2))
    (htc : ∀ i, kap+3 ≤ i → i ≤ ell → 1 ≤ w i)
    (hlinear : ∀ i, kap+3 ≤ i → i ≤ ell → i-kap-2 ≤ w i) :
    n-(if t=kap-1 then kap else kap+1)-2 ≤
      window w t n+(if n=t+1 then 1 else 0)-(if n=t+2 then 1 else 0) := by
  have hz : ∀ i, i ≤ n-1 → 0 ≤ w i := fun i hi => hzero i (by omega)
  by_cases hstat : t=kap-1
  · simp only [ite_eq_left hstat] at hstart ⊢
    have hplus : n ≠ t+1 := by omega
    have hminus : n ≠ t+2 := by omega
    simp only [ite_eq_right hplus, ite_eq_right hminus, add_zero, sub_zero]
    by_cases hfirst : n=kap+3
    · have hs : w (kap+2) ≤ window w t n := by
        exact Finset.single_le_sum (fun i hi => hz i (Finset.mem_Icc.mp hi).2)
          (Finset.mem_Icc.mpr (show n-t ≤ kap+2 ∧ kap+2 ≤ n-1 by constructor <;> omega))
      have hh := hoffset (by omega)
      omega
    · by_cases hsecond : n=kap+4
      · have hs := two_window_terms w t n (kap+3) (kap+2) (by omega) (by omega) (by omega) hz
        have h1 := htc (kap+3) (by omega) (by omega)
        have h2 := hoffset (by omega)
        omega
      · have hs := two_window_terms w t n (n-1) (n-2) (by omega) (by omega) (by omega) hz
        have h1 := hlinear (n-1) (by omega) hend
        have h2 := htc (n-2) (by omega) (by omega)
        omega
  · simp only [ite_eq_right hstat] at hstart ⊢
    have h1 := hlinear (n-1) (by omega) hend
    by_cases hdent : n=t+2
    · have hs := two_window_terms w t n (n-1) kap (by omega) (by omega) (by omega) hz
      have hplus : n ≠ t+1 := by omega
      simp only [ite_eq_left hdent, ite_eq_right hplus]
      omega
    · have hs : w (n-1) ≤ window w t n := by
        exact Finset.single_le_sum (fun i hi => hz i (Finset.mem_Icc.mp hi).2)
          (Finset.mem_Icc.mpr (show n-t ≤ n-1 ∧ n-1 ≤ n-1 by constructor <;> omega))
      simp only [ite_eq_right hdent]
      split_ifs <;> omega

theorem unit_multiplicities_second_overlap (etaX etaY sx sy : ℤ)
    (hx : 1+etaX ≤ sx) (hy : 1+etaY ≤ sy) : etaX+etaY ≤ sx+sy := by omega

#print axioms two_window_terms
#print axioms three_window_terms
#print axioms joint_pre_peak_window_payment
#print axioms exponential_joint_budget
#print axioms large_peak_pays_joint
#print axioms low_joint_peak_failure_region
#print axioms offset_linear_peak_payment
#print axioms linear_pre_peak_window_payment
#print axioms unit_multiplicities_second_overlap

end JointSourceGrowth
