import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ActualDyadicSlopeNorm
noncomputable section

def rho : ℝ := 3/5
def base : ℝ := 35/32
def offset : ℝ := 125/22
def stepEval (t : ℕ) : ℝ := (3/2)*(1-rho^t)

theorem whole_capacity_eval_bounds (t : ℕ) (ht : 2 ≤ t) :
    0 ≤ stepEval t ∧ stepEval t ≤ base^(t-1) ∧ stepEval t ≤ 3/2 ∧
    (3 ≤ t → 147/125 ≤ stepEval t) := by
  have hp0 : 0 ≤ rho^t := pow_nonneg (by norm_num [rho]) t
  have hp1 : rho^t ≤ 1 := pow_le_one₀ (by norm_num [rho]) (by norm_num [rho])
  have hs0 : 0 ≤ stepEval t := by dsimp [stepEval]; nlinarith
  have hs1 : stepEval t ≤ 3/2 := by dsimp [stepEval]; nlinarith
  refine ⟨hs0, ?_, hs1, ?_⟩
  · by_cases hsmall : t ≤ 5
    · interval_cases t <;> norm_num [stepEval,rho,base]
    · have h5 : 5 ≤ t-1 := by omega
      have hpow := pow_le_pow_right₀ (show (1:ℝ) ≤ base by norm_num [base]) h5
      have hbase : (3:ℝ)/2 ≤ base^5 := by norm_num [base]
      linarith
  · intro ht3
    have hp := pow_le_pow_of_le_one (show (0:ℝ) ≤ rho by norm_num [rho])
      (show rho ≤ 1 by norm_num [rho]) ht3
    have hcube : rho^3=(27:ℝ)/125 := by norm_num [rho]
    rw [hcube] at hp
    dsimp [stepEval]
    linarith

def run (word : List ℕ) (f : ℝ) : ℝ :=
  word.foldl (fun value t => 1+stepEval t*value) f
def degree (word : List ℕ) : ℕ := (word.map (fun t => t-1)).sum

private theorem one_step_invariant (M t : ℕ) (f : ℝ)
    (ht : 2 ≤ t) (hin : f+offset ≤ 10*base^M) :
    (1+stepEval t*f)+offset ≤ 10*base^(M+(t-1)) := by
  have hb : (1:ℝ) ≤ base := by norm_num [base]
  have hM : (1:ℝ) ≤ base^M := one_le_pow₀ hb
  obtain ⟨hs0,hsbound,_,hs3⟩ := whole_capacity_eval_bounds t ht
  rw [pow_add]
  by_cases ht2 : t=2
  · subst t
    norm_num [stepEval,rho,base,offset] at *
    nlinarith
  · have ht3 : 3 ≤ t := by omega
    have hpay : (1:ℝ) ≤ offset*(stepEval t-1) := by
      have hg := hs3 ht3
      norm_num [offset] at *
      nlinarith
    calc
      1+stepEval t*f+offset ≤ stepEval t*(f+offset) := by nlinarith
      _ ≤ stepEval t*(10*base^M) := mul_le_mul_of_nonneg_left hin hs0
      _ ≤ 10*(base^M*base^(t-1)) := by
        have h := mul_le_mul_of_nonneg_left hsbound (show 0 ≤ 10*base^M by positivity)
        nlinarith

theorem whole_arbitrary_capacity_fold_invariant (word : List ℕ) (M : ℕ) (f : ℝ)
    (hword : ∀ t ∈ word, 2 ≤ t) (hin : f+offset ≤ 10*base^M) :
    run word f+offset ≤ 10*base^(M+degree word) := by
  induction word generalizing M f with
  | nil => simpa [run,degree] using hin
  | cons t word ih =>
    have ht : 2 ≤ t := hword t (by simp)
    have hrest : ∀ u ∈ word, 2 ≤ u := by
      intro u hu
      exact hword u (by simp [hu])
    have hstep := one_step_invariant M t f ht hin
    have hwhole := ih (M+(t-1)) (1+stepEval t*f) hrest hstep
    simpa [run,degree,List.foldl_cons,Nat.add_assoc] using hwhole

theorem whole_actual_seed_and_word_norm (alpha : ℕ) (word : List ℕ) (f : ℝ)
    (hword : ∀ t ∈ word, 2 ≤ t) (hseed : f ≤ 5/2) :
    run word f+offset ≤ 10*base^(alpha+degree word) := by
  apply whole_arbitrary_capacity_fold_invariant word alpha f hword
  have hM : (1:ℝ) ≤ base^alpha := one_le_pow₀ (by norm_num [base])
  norm_num [offset] at *
  nlinarith

theorem whole_arbitrary_tail_preserves_plus_two (word : List ℕ) (f : ℝ)
    (hword : ∀ t ∈ word, 2 ≤ t) (hf : 0 ≤ f) :
    run word f+2 ≤ ((3:ℝ)/2)^word.length*(f+2) := by
  induction word generalizing f with
  | nil => simp [run]
  | cons t word ih =>
    have ht : 2 ≤ t := hword t (by simp)
    obtain ⟨hs0,_,hs1,_⟩ := whole_capacity_eval_bounds t ht
    have hrest : ∀ u ∈ word, 2 ≤ u := by
      intro u hu
      exact hword u (by simp [hu])
    have hfnew : 0 ≤ 1+stepEval t*f := by positivity
    have htail := ih (1+stepEval t*f) hrest hfnew
    have hfirst : (1+stepEval t*f)+2 ≤ (3/2)*(f+2) := by
      nlinarith [mul_le_mul_of_nonneg_right hs1 hf]
    have hmul := mul_le_mul_of_nonneg_left hfirst
      (show 0 ≤ ((3:ℝ)/2)^word.length by positivity)
    simp only [run,List.foldl_cons,List.length_cons,pow_succ] at *
    nlinarith

#print axioms whole_capacity_eval_bounds
#print axioms whole_arbitrary_capacity_fold_invariant
#print axioms whole_actual_seed_and_word_norm
#print axioms whole_arbitrary_tail_preserves_plus_two
end
end ActualDyadicSlopeNorm
