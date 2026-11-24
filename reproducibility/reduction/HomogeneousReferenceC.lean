import Mathlib

set_option maxHeartbeats 0
open scoped goldenRatio
namespace HomogeneousReferenceC

noncomputable def minusWindow (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (-φ)^(j+1)

noncomputable def plusWindow (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (φ-1)^(j+1)

private theorem inverse_phi : φ*(φ-1)=1 := by
  nlinarith [Real.goldenRatio_sq]

private theorem minus_identity (t : ℕ) : φ*minusWindow t=(-φ)^t-1 := by
  induction t with
  | zero => simp [minusWindow]
  | succ t ih =>
    have hs : minusWindow (t+1)=minusWindow t+(-φ)^(t+1) :=
      Finset.sum_range_succ _ _
    have hm := congrArg (fun x : ℝ => x*((-φ)^t)) Real.goldenRatio_sq
    rw [hs,pow_succ]
    nlinarith only [ih,hm]

private theorem plus_identity (t : ℕ) : φ^t*plusWindow t=φ*(φ^t-1) := by
  induction t with
  | zero => simp [plusWindow]
  | succ t ih =>
    have hs : plusWindow (t+1)=plusWindow t+(φ-1)^(t+1) :=
      Finset.sum_range_succ _ _
    have hp : φ^(t+1)*(φ-1)^(t+1)=1 := by
      rw [← mul_pow,inverse_phi,one_pow]
    have hh := congrArg (fun x : ℝ => φ*x) ih
    rw [hs,mul_add,pow_succ]
    rw [pow_succ] at hp
    nlinarith only [hp,hh,Real.goldenRatio_sq]

private theorem plus_pos (t : ℕ) (ht : 1 ≤ t) : 0 < plusWindow t := by
  have hq : 0 < φ-1 := by linarith [Real.one_lt_goldenRatio]
  have hs := Finset.single_le_sum (s:=Finset.range t)
    (f:=fun j => (φ-1)^(j+1))
    (fun j _ => pow_nonneg (le_of_lt hq) _) (show 0 ∈ Finset.range t by simp; omega)
  simp only [zero_add,pow_one] at hs
  exact lt_of_lt_of_le hq hs

theorem all_capacity_relative_spectral_bound (t : ℕ) (ht : 2 ≤ t) :
    φ*|minusWindow t| ≤ φ^t*plusWindow t := by
  have hphi := Real.goldenRatio_pos
  by_cases htwo : t=2
  · subst t
    have hm : minusWindow 2=1 := by
      norm_num [minusWindow,Finset.sum_range_succ]
    have hp : plusWindow 2=1 := by
      norm_num [plusWindow,Finset.sum_range_succ]
      nlinarith only [Real.goldenRatio_sq]
    rw [hm,hp,abs_one,mul_one,mul_one,Real.goldenRatio_sq]
    linarith
  have ht3 : 3 ≤ t := by omega
  have hident := congrArg abs (minus_identity t)
  simp only [abs_mul,abs_of_pos hphi] at hident
  have htri : |(-φ)^t-1| ≤ φ^t+1 := by
    calc
      |(-φ)^t-1| = |(-φ)^t+(-1)| := rfl
      _ ≤ |(-φ)^t|+|(-1:ℝ)| := abs_add_le _ _
      _ = φ^t+1 := by simp [abs_pow,abs_of_pos hphi]
  have hpow : φ^3 ≤ φ^t := pow_le_pow_right₀
    (le_of_lt Real.one_lt_goldenRatio) ht3
  have hcube : φ^3=2*φ+1 := by
    rw [pow_succ,Real.goldenRatio_sq]
    nlinarith only [Real.goldenRatio_sq]
  have hmul := mul_nonneg (show 0 ≤ φ-1 by linarith [Real.one_lt_goldenRatio])
    (show 0 ≤ φ^t-φ^3 by linarith only [hpow])
  rw [hcube] at hmul
  rw [plus_identity]
  nlinarith only [hident,htri,hmul,Real.goldenRatio_sq]

noncomputable def plusWord : List ℕ → ℝ
  | [] => 1
  | t::V => plusWindow t*plusWord V

noncomputable def minusWord : List ℕ → ℝ
  | [] => 1
  | t::V => minusWindow t*minusWord V

private theorem word_plus_pos (V : List ℕ) (hV : ∀ t ∈ V, 2 ≤ t) :
    0 < plusWord V := by
  induction V with
  | nil => simp [plusWord]
  | cons t V ih =>
    exact mul_pos (plus_pos t (by have := hV t (by simp); omega))
      (ih (by intro x hx; exact hV x (by simp [hx])))

theorem entire_word_relative_spectral_bound (V : List ℕ)
    (hV : ∀ t ∈ V, 2 ≤ t) :
    φ^V.length*|minusWord V| ≤ φ^V.sum*plusWord V := by
  induction V with
  | nil => simp [plusWord,minusWord]
  | cons t V ih =>
    have ht := all_capacity_relative_spectral_bound t (hV t (by simp))
    have hv := ih (by intro x hx; exact hV x (by simp [hx]))
    have hh := mul_le_mul ht hv
      (mul_nonneg (by positivity) (abs_nonneg _))
      (mul_nonneg (by positivity) (le_of_lt (plus_pos t (by have := hV t (by simp); omega))))
    simp only [List.length_cons,List.sum_cons,plusWord,minusWord,abs_mul,
      pow_add,pow_one] at *
    nlinarith only [hh]

theorem entire_word_homogeneous_rank_budget (V : List ℕ)
    (hV : ∀ t ∈ V, 2 ≤ t) (hcount : 2 ≤ V.length)
    (N : ℕ) (hN : V.sum+2 ≤ N) (hN4 : 4 ≤ N) :
    |minusWord V| ≤ φ^(N-4)*plusWord V := by
  have hfull := entire_word_relative_spectral_bound V hV
  have htwo : φ^2 ≤ φ^V.length :=
    pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) hcount
  have hpow : φ^V.sum ≤ φ^((N-4)+2) :=
    pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) (by omega)
  have ha := word_plus_pos V hV
  have hh := mul_le_mul_of_nonneg_right htwo (abs_nonneg (minusWord V))
  have hj := mul_le_mul_of_nonneg_right hpow (le_of_lt ha)
  rw [pow_add] at hj
  have hx : φ^2*|minusWord V| ≤ φ^2*(φ^(N-4)*plusWord V) := by
    nlinarith only [hh,hfull,hj]
  exact (mul_le_mul_iff_right₀ (show 0 < φ^2 by positivity)).mp hx

theorem entire_convolution_ratio_envelope (s : Finset ℕ) (B : ℕ → ℝ)
    (g : ℤ → ℝ) (k : ℤ) (a b : ℝ)
    (hB : ∀ i ∈ s, 0 ≤ B i)
    (hg : ∀ i ∈ s, g (k-i)*b ≥ g (k-i-1)*a) :
    (∑ i ∈ s, B i*g (k-i))*b ≥ (∑ i ∈ s, B i*g (k-i-1))*a := by
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hh := mul_le_mul_of_nonneg_left (hg i hi) (hB i hi)
  nlinarith only [hh]

theorem spectral_determinant_nonnegative (A C x y z sigma p : ℝ)
    (_hA : 0 ≤ A) (hp : 0 ≤ p) (hx : 1 ≤ x) (hy : y=p*z)
    (hsigma : sigma ≤ 1) (hsign : sigma*C ≤ |C|)
    (hbudget : |C| ≤ A*z) :
    0 ≤ A*y*(x-sigma)-sigma*C*p*(x-1) := by
  have hmult := mul_le_mul_of_nonneg_right (le_trans hsign hbudget)
    (show 0 ≤ p*(x-1) from mul_nonneg hp (by linarith only [hx]))
  have hy0 : 0 ≤ A*y := by
    have hz : 0 ≤ A*z := le_trans (abs_nonneg C) hbudget
    rw [hy]
    nlinarith only [mul_nonneg hp hz]
  have hn := mul_nonneg hy0 (show 0 ≤ 1-sigma by linarith only [hsigma])
  rw [hy] at hn ⊢
  nlinarith only [hmult,hn]

theorem alternating_first_defect_LC_boundary (A delta prev : ℝ)
    (hA : 0 ≤ A) (hd : 1 ≤ delta) (hp : A ≤ prev) :
    0 ≤ -A+delta*prev := by
  have hp0 : 0 ≤ prev := le_trans hA hp
  have hh := mul_nonneg (show 0 ≤ delta-1 by linarith only [hd]) hp0
  nlinarith only [hh,hp]

theorem later_ordinary_seed_exact_payment (b c d delta A : ℝ)
    (hrec : d=b+c) (hCassini : c^2-b*d=A) :
    c*(c+d)-d*(d-delta)=A+delta*d := by
  rw [← hCassini]
  rw [hrec]
  ring

theorem simultaneous_finite_read_integration (F D G : ℕ → ℝ)
    (lambda : ℝ) (a b : ℕ) (_hab : a ≤ b)
    (hF : F (a+1) ≥ lambda*F a)
    (hG : G (a+1) ≥ lambda*G a)
    (hD : ∀ i, a+2 ≤ i → i ≤ b+1 → D i ≥ lambda*D (i-1))
    (hFD : ∀ i, a+1 ≤ i → i ≤ b+1 → F i=F (i-1)+D i)
    (hGD : ∀ i, a+1 ≤ i → i ≤ b+1 → G i=G (i-1)+F i) :
    ∀ i, a+1 ≤ i → i ≤ b+1 →
      F i ≥ lambda*F (i-1) ∧ G i ≥ lambda*G (i-1) := by
  intro i hia hib
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases he : i=a+1
    · subst i
      simpa using And.intro hF hG
    have hil : a+2 ≤ i := by omega
    have hj := ih (i-1) (by omega) (by omega) (by omega)
    have hd := hD i hil hib
    have hfcur := hFD i (by omega) hib
    have hfprev : F (i-1)=F (i-2)+D (i-1) := by
      simpa [Nat.sub_sub] using hFD (i-1) (by omega) (by omega)
    have hf : F i ≥ lambda*F (i-1) := by
      have hjf := hj.1
      have hjf' : F (i-1) ≥ lambda*F (i-2) := by
        simpa only [Nat.sub_sub,Nat.reduceAdd] using hjf
      calc
        F i = F (i-1)+D i := hfcur
        _ ≥ lambda*F (i-2)+lambda*D (i-1) := add_le_add hjf' hd
        _ = lambda*(F (i-2)+D (i-1)) := by ring
        _ = lambda*F (i-1) := by rw [← hfprev]
    have hgcur := hGD i (by omega) hib
    have hgprev : G (i-1)=G (i-2)+F (i-1) := by
      simpa [Nat.sub_sub] using hGD (i-1) (by omega) (by omega)
    have hg : G i ≥ lambda*G (i-1) := by
      have hjg := hj.2
      have hjg' : G (i-1) ≥ lambda*G (i-2) := by
        simpa only [Nat.sub_sub,Nat.reduceAdd] using hjg
      calc
        G i = G (i-1)+F i := hgcur
        _ ≥ lambda*G (i-2)+lambda*F (i-1) := add_le_add hjg' hf
        _ = lambda*(G (i-2)+F (i-1)) := by ring
        _ = lambda*G (i-1) := by rw [← hgprev]
    exact ⟨hf,hg⟩

#print axioms all_capacity_relative_spectral_bound
#print axioms entire_word_relative_spectral_bound
#print axioms entire_word_homogeneous_rank_budget
#print axioms entire_convolution_ratio_envelope
#print axioms spectral_determinant_nonnegative
#print axioms alternating_first_defect_LC_boundary
#print axioms later_ordinary_seed_exact_payment
#print axioms simultaneous_finite_read_integration

end HomogeneousReferenceC
