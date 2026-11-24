import Mathlib

/- Finite-chain, crossing-window and isolated-source kernels for the written
   unbounded actual sorted-arm induction. No end-to-end actual-arm encoding. -/

namespace SourceCurvatureSingleNotch

private theorem chain (w : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b)
    (hs : ∀ i, a ≤ i → i < b → w i ≤ w (i+1)) : w a ≤ w b := by
  revert hs
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hk ih =>
      intro hs
      exact (ih (fun i hi hik => hs i hi (by omega))).trans (hs k hk (by omega))

theorem record_after_single_notch (w : ℕ → ℤ) (L ell : ℕ)
    (hzero : ∀ i, i ≤ 2 → w i=0)
    (hpos : ∀ i, i ≤ ell → 0 ≤ w i)
    (hstep : ∀ n, 3 ≤ n → n ≤ ell → n ≠ L+2 → w (n-1) ≤ w n)
    (hrecover : L+3 ≤ ell → w (L+1) ≤ w (L+3))
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ ell) (hL : L+3 ≤ j) : w i ≤ w j := by
  by_cases hi : i ≤ 2
  · rw [hzero i hi]
    exact hpos j hj
  · have post : ∀ a b, L+2 ≤ a → a ≤ b → b ≤ ell → w a ≤ w b := by
      intro a b ha hab hb
      apply chain w a b hab
      intro n hn hnb
      have hs := hstep (n+1) (by omega) (by omega) (by omega)
      simpa using hs
    by_cases hbefore : i ≤ L+1
    · have hpre : w i ≤ w (L+1) := by
        apply chain w i (L+1) hbefore
        intro n hn hnb
        have hs := hstep (n+1) (by omega) (by omega) (by omega)
        simpa using hs
      exact hpre.trans ((hrecover (by omega)).trans (post (L+3) j (by omega) hL hj))
    · exact post i j (by omega) hij hj

theorem spaced_source_comparison (w : ℕ → ℤ) (L ell i j t : ℕ)
    (hzero : ∀ a, a ≤ 2 → w a=0) (hpos : 0 ≤ w j)
    (hrecord : ∀ a b, a ≤ b → b ≤ ell → L+3 ≤ b → w a ≤ w b)
    (ht : L ≤ t) (hspan : i+t=j) (hj : j ≤ ell) : w i ≤ w j := by
  by_cases hi : i ≤ 2
  · rw [hzero i hi]; exact hpos
  · exact hrecord i j (by omega) hj (by omega)

theorem crossing_window_source_order (D w : ℕ → ℤ) (ell R L t n : ℕ)
    (hL : 2 ≤ L) (ht : L ≤ t) (hn : 3 ≤ n)
    (hR : n-1 ≤ R) (hstrict : D (n-t-1) < D (n-1))
    (hzero : ∀ a, a ≤ 2 → w a=0)
    (hpos : ∀ a, a ≤ R → 0 ≤ w a)
    (hformula : ∀ a, 3 ≤ a → a ≤ R → w a=2*D (a-1)-D a)
    (hrise : MonotoneOn D (Set.Icc 2 ell))
    (hfall : AntitoneOn D (Set.Icc ell R))
    (hrecord : ∀ a b, a ≤ b → b ≤ ell → L+3 ≤ b → w a ≤ w b) :
    w (n-t-1) ≤ w (n-1) := by
  let i := n-t-1
  let j := n-1
  change w i ≤ w j
  change D i < D j at hstrict
  change j ≤ R at hR
  have hij : i ≤ j := by dsimp [i,j]; omega
  by_cases hi : i ≤ 2
  · rw [hzero i hi]
    exact hpos j hR
  · have hspan : i+t=j := by dsimp [i,j] at *; omega
    by_cases hj : j ≤ ell
    · exact spaced_source_comparison w L ell i j t hzero (hpos j hR) hrecord ht hspan hj
    · have hil : i < ell := by
        by_contra! hle
        have hh := hfall (show i ∈ Set.Icc ell R by constructor <;> omega)
          (show j ∈ Set.Icc ell R by constructor <;> omega) hij
        omega
      have hdi := hrise (show i-1 ∈ Set.Icc 2 ell by constructor <;> omega)
        (show i ∈ Set.Icc 2 ell by constructor <;> omega) (by omega : i-1 ≤ i)
      have hdj := hfall (show j-1 ∈ Set.Icc ell R by constructor <;> omega)
        (show j ∈ Set.Icc ell R by constructor <;> omega) (by omega : j-1 ≤ j)
      have hwi := hformula i (by omega) (by omega)
      have hwj := hformula j (by omega) hR
      omega

theorem isolated_source_second_difference (head leave value : ℤ) (n t : ℕ)
    (hcomp : leave ≤ head)
    (hid : value=head-leave+(if n=t+1 then 1 else 0)-
      2*(if n=t+2 then 1 else 0)+(if n=t+3 then 1 else 0))
    (hne : n ≠ t+2) : 0 ≤ value := by
  simp only [ite_eq_right hne] at hid
  split_ifs at hid <;> omega

theorem immediate_recovery_payment (w : ℕ → ℤ) (kap t R : ℕ)
    (ht : kap-1 ≤ t) (hkap : 3 ≤ kap) (hR : t+2 ≤ R)
    (hpos : ∀ i, i ≤ R → 0 ≤ w i)
    (hbirth : 1 ≤ w kap)
    (hlate : ∀ i, kap+2 ≤ i → i ≤ R → 1 ≤ w i) :
    0 ≤ w (t+1)+w (t+2)-1 := by
  have h1 := hpos (t+1) (by omega)
  have h2 := hpos (t+2) hR
  by_cases heq : t=kap-1
  · have hid : t+1=kap := by omega
    rw [hid]
    omega
  · have hl := hlate (t+2) (by omega) hR
    omega

theorem actual_family_source_dip (T left right : ℤ)
    (hl : left=2*T-2) (hr : right=2*T-3) : right=left-1 ∧ right<left := by omega

def coeff (p : List ℕ) (n : ℕ) : ℕ := p[n]?.getD 0
def actualAppend (p : List ℕ) (t : ℕ) : List ℕ :=
  1::((List.range (p.length+t-1)).map fun n =>
    ((List.range (min t (n+1))).map fun j => coeff p (n-j)).sum)
def derivative (p : List ℕ) (n : ℕ) : ℕ :=
  if 2 ≤ n then coeff p n-coeff p (n-1) else 0
def curvature (p : List ℕ) (n : ℕ) : ℤ :=
  3*(coeff p (n-1):ℤ)-(coeff p n:ℤ)-2*(coeff p (n-2):ℤ)

theorem exact_actual_counterexample_member :
    let p := actualAppend (actualAppend (actualAppend (List.replicate 7 1) 2) 6) 7
    derivative p 9=11 ∧
    (List.range 9).all (fun i => decide (derivative p i<11))=true ∧
    (List.range (p.length+1)).all (fun i => decide (derivative p i≤11))=true ∧
    curvature p 8=10 ∧ curvature p 9=9 := by decide

#print axioms record_after_single_notch
#print axioms spaced_source_comparison
#print axioms crossing_window_source_order
#print axioms isolated_source_second_difference
#print axioms immediate_recovery_payment
#print axioms actual_family_source_dip
#print axioms exact_actual_counterexample_member

end SourceCurvatureSingleNotch
