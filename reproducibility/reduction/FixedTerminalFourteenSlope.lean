import ActualDyadicSlopeNorm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace FixedTerminalFourteenSlope
open ActualDyadicSlopeNorm
noncomputable section
def ratio : ℝ := 6125/6144
def shortRatio : ℝ := 175/192
def relative (t : ℕ) : ℝ := stepEval t/base^(t-1)
def stepProduct (word : List ℕ) : ℝ := (word.map stepEval).prod

private theorem all_step_nonnegative (t : ℕ) : 0 ≤ stepEval t := by
  have hp : rho^t ≤ 1 := pow_le_one₀ (by norm_num [rho]) (by norm_num [rho])
  dsimp [stepEval]
  linarith

theorem whole_large_capacity_offset_contraction (word : List ℕ) (f : ℝ)
    (hword : ∀ t ∈ word, 3 ≤ t) :
    run word f+offset ≤ (f+offset)*stepProduct word := by
  induction word generalizing f with
  | nil => simp [run,stepProduct]
  | cons t word ih =>
    have ht : 3 ≤ t := hword t (by simp)
    have hrest : ∀ u ∈ word, 3 ≤ u := by
      intro u hu
      exact hword u (by simp [hu])
    have hnorm := (whole_capacity_eval_bounds t (by omega)).2.2.2 ht
    have hpay : (1:ℝ) ≤ offset*(stepEval t-1) := by
      norm_num [offset] at *
      nlinarith
    have hfirst : 1+stepEval t*f+offset ≤ stepEval t*(f+offset) := by nlinarith
    have hp0 : 0 ≤ stepProduct word := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
      exact all_step_nonnegative u
    have hwhole := ih (1+stepEval t*f) hrest
    have hm := mul_le_mul_of_nonneg_right hfirst hp0
    simp only [run,List.foldl_cons,stepProduct,List.map_cons,List.prod_cons] at *
    nlinarith

private theorem relative_step (t : ℕ) (ht : 4 ≤ t) : relative (t+1) ≤ relative t := by
  have hr0 : (0:ℝ) ≤ rho := by norm_num [rho]
  have hr1 : rho ≤ 1 := by norm_num [rho]
  have hpow := pow_le_pow_of_le_one hr0 hr1 (show 5 ≤ t+1 by omega)
  have hpow4 := pow_le_pow_of_le_one hr0 hr1 ht
  have hmono : stepEval 4 ≤ stepEval t := by dsimp [stepEval]; nlinarith
  have hbase : rho^5 ≤ (base-1)*stepEval 4 := by norm_num [rho,base,stepEval]
  have hmul := mul_le_mul_of_nonneg_left hmono (show 0 ≤ base-1 by norm_num [base])
  have hrec : stepEval (t+1)=stepEval t+rho^(t+1) := by
    dsimp [stepEval]
    rw [pow_succ]
    dsimp [rho]
    ring_nf
  have hs : stepEval (t+1) ≤ base*stepEval t := by nlinarith
  have hb0 : (0:ℝ) < base := by norm_num [base]
  have he : base^t=base^(t-1)*base := by
    have ht' : t=(t-1)+1 := by omega
    calc
      base^t=base^((t-1)+1) := congrArg (fun k : ℕ => base^k) ht'
      _ = base^(t-1)*base := pow_succ _ _
  simp only [relative,Nat.add_sub_cancel]
  apply (div_le_div_iff₀ (pow_pos hb0 t) (pow_pos hb0 (t-1))).mpr
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (le_of_lt hb0) (t-1))
  rw [he]
  nlinarith

private theorem relative_antitone (L t : ℕ) (hL : 4 ≤ L) (ht : L ≤ t) :
    relative t ≤ relative L := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => exact (relative_step t (by omega)).trans ih

theorem whole_relative_capacity_envelope (L t : ℕ) (hL : 3 ≤ L) (ht : L ≤ t) :
    relative t ≤ relative (max 4 L) := by
  by_cases hL3 : L=3
  · subst L
    simp only [max_eq_left (show 3 ≤ 4 by omega)]
    by_cases ht3 : t=3
    · subst t
      norm_num [relative,stepEval,base,rho]
    · exact relative_antitone 4 t (by omega) (by omega)
  · have hL4 : 4 ≤ L := by omega
    rw [max_eq_right hL4]
    exact relative_antitone L t hL4 ht

private theorem slow_block_weight (a : ℕ) :
    ((a:ℝ)+1)*((20:ℝ)/21)^a ≤ 8 := by
  by_cases ha : a ≤ 19
  · interval_cases a <;> norm_num
  · have ha19 : 19 ≤ a := by omega
    clear ha
    induction a, ha19 using Nat.le_induction with
    | base => norm_num
    | succ a ha ih =>
      have haR : (19:ℝ) ≤ a := by exact_mod_cast ha
      have hf : ((20:ℝ)/21)*((a:ℝ)+2) ≤ (a:ℝ)+1 := by nlinarith
      have hp : (0:ℝ) ≤ ((20:ℝ)/21)^a := by positivity
      have hm := mul_le_mul_of_nonneg_left hf hp
      push_cast
      rw [pow_succ]
      nlinarith

theorem whole_sixteen_power_block (m : ℕ) : (m:ℝ)*ratio^m ≤ 128 := by
  have h0 : (0:ℝ) ≤ ratio := by norm_num [ratio]
  have h1 : ratio ≤ 1 := by norm_num [ratio]
  have hblock : ratio^16 ≤ (20:ℝ)/21 := by norm_num [ratio]
  let a := m/16
  let r := m%16
  have hr : r < 16 := Nat.mod_lt _ (by norm_num)
  have hm : 16*a+r=m := by simpa [a,r,Nat.mul_comm] using Nat.div_add_mod m 16
  have hpow : ratio^m ≤ ((20:ℝ)/21)^a := by
    rw [←hm,pow_add,pow_mul]
    have hpa := pow_le_pow_left₀ (pow_nonneg h0 16) hblock a
    have hpr : ratio^r ≤ 1 := pow_le_one₀ h0 h1
    nlinarith [mul_le_mul hpa hpr (pow_nonneg h0 r) (show 0 ≤ ((20:ℝ)/21)^a by positivity)]
  have hm_nat : m ≤ 16*(a+1) := by omega
  have hm_real : (m:ℝ) ≤ 16*((a:ℝ)+1) := by exact_mod_cast hm_nat
  have hw := slow_block_weight a
  have hp := mul_le_mul hm_real hpow (pow_nonneg h0 m)
    (show 0 ≤ 16*((a:ℝ)+1) by positivity)
  nlinarith

private theorem negative_binomial_point (i : ℕ) : ((i:ℝ)+1)*rho^i ≤ 6/5 := by
  by_cases hi0 : i=0
  · subst i; norm_num [rho]
  · have hi : 1 ≤ i := by omega
    clear hi0
    induction i, hi using Nat.le_induction with
    | base => norm_num [rho]
    | succ i hi ih =>
      have hiR : (1:ℝ) ≤ i := by exact_mod_cast hi
      have hf : rho*((i:ℝ)+2) ≤ (i:ℝ)+1 := by norm_num [rho]; nlinarith
      have hm := mul_le_mul_of_nonneg_left hf (pow_nonneg (show 0 ≤ rho by norm_num [rho]) i)
      push_cast
      rw [pow_succ]
      nlinarith

theorem whole_two_interval_weighted_coefficients (kernel : ℕ → ℝ)
    (hk : ∀ i, kernel i ≤ (i:ℝ)+1) (i : ℕ) : kernel i*rho^i ≤ 6/5 := by
  have h := mul_le_mul_of_nonneg_right (hk i) (pow_nonneg (show 0 ≤ rho by norm_num [rho]) i)
  exact h.trans (negative_binomial_point i)

theorem whole_weighted_finite_convolution (kernel G : ℕ → ℝ) (n : ℕ) (mass : ℝ)
    (hG : ∀ i, 0 ≤ G i) (hk : ∀ i ≤ n, kernel i*rho^i ≤ 6/5)
    (hMass : (∑ j ∈ Finset.range (n+1), G j*rho^j) ≤ mass) :
    rho^n*(∑ i ∈ Finset.range (n+1), kernel i*G (n-i)) ≤ (6/5)*mass := by
  have hterm : ∀ i ∈ Finset.range (n+1),
      kernel i*G (n-i)*rho^n ≤ (6/5)*(G (n-i)*rho^(n-i)) := by
    intro i hi
    have hin : i ≤ n := by have h := Finset.mem_range.mp hi; omega
    have he : i+(n-i)=n := by omega
    have hp := pow_add rho i (n-i)
    rw [he] at hp
    have hm := mul_le_mul_of_nonneg_right (hk i hin)
      (show 0 ≤ G (n-i)*rho^(n-i) by exact mul_nonneg (hG _) (pow_nonneg (by norm_num [rho]) _))
    rw [hp]
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  have hreflect : (∑ i ∈ Finset.range (n+1), G (n-i)*rho^(n-i))=
      ∑ j ∈ Finset.range (n+1), G j*rho^j := by
    simpa using Finset.sum_range_reflect (fun j => G j*rho^j) (n+1)
  calc
    rho^n*(∑ i ∈ Finset.range (n+1), kernel i*G (n-i))=
        ∑ i ∈ Finset.range (n+1), kernel i*G (n-i)*rho^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ ≤ (6/5)*(∑ i ∈ Finset.range (n+1), G (n-i)*rho^(n-i)) := by
      simpa [Finset.mul_sum] using hsum
    _ = (6/5)*(∑ j ∈ Finset.range (n+1), G j*rho^j) := by rw [hreflect]
    _ ≤ (6/5)*mass := mul_le_mul_of_nonneg_left hMass (by norm_num)

def constantProduct : ℝ := ∏ i ∈ Finset.range 10, relative (max 4 (i+3))

theorem whole_fixed_terminal_product_budget (T : ℕ → ℕ)
    (hT : ∀ i < 10, i+3 ≤ T i) :
    0 ≤ (∏ i ∈ Finset.range 10, relative (T i)) ∧
    (41472/125:ℝ)*(∏ i ∈ Finset.range 10, relative (T i)) ≤ base^39 := by
  have hp0 : 0 ≤ (∏ i ∈ Finset.range 10, relative (T i)) := by
    apply Finset.prod_nonneg
    intro i _
    exact div_nonneg (all_step_nonnegative _) (pow_nonneg (by norm_num [base]) _)
  have hprod : (∏ i ∈ Finset.range 10, relative (T i)) ≤ constantProduct := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact div_nonneg (all_step_nonnegative _) (pow_nonneg (by norm_num [base]) _)
    · intro i hi
      exact whole_relative_capacity_envelope (i+3) (T i) (by omega) (hT i (Finset.mem_range.mp hi))
  have hconstant : (41472/125:ℝ)*constantProduct ≤ base^39 := by
    norm_num [constantProduct,Finset.prod_range_succ,relative,stepEval,base,rho]
  exact ⟨hp0,(mul_le_mul_of_nonneg_left hprod (by norm_num)).trans hconstant⟩

theorem whole_fixed_template_support_and_degree_guards (K M A u T m : ℕ)
    (hK : 16 ≤ K) (hA : 6 ≤ A) (hu : 2 ≤ u) (hT : u ≤ T)
    (hM : M=A+(u-1)+(T-1)) (hbulk : M ≤ 2*m) :
    u < m-1 ∧ 3 ≤ m ∧ 92 ≤ 1+(K-3)*(K-2)/2 ∧
    K-4 ≤ (1+(K-2)*(K-1)/2)/2 := by
  have hprod : 13*14 ≤ (K-3)*(K-2) := Nat.mul_le_mul (by omega) (by omega)
  have hquad : 4*(K-2) ≤ (K-2)*(K-1) := by
    have h := Nat.mul_le_mul_left (K-2) (show 4 ≤ K-1 by omega)
    simpa [Nat.mul_comm] using h
  omega

theorem whole_large_read_from_eighty (j : ℕ) (hj : 80 ≤ j) :
    10*((j:ℝ)+1)*shortRatio^j ≤ 1 := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [shortRatio]
  | succ j hj ih =>
    have hjR : (80:ℝ) ≤ j := by exact_mod_cast hj
    have hf : shortRatio*((j:ℝ)+2) ≤ (j:ℝ)+1 := by norm_num [shortRatio]; nlinarith
    have hm := mul_le_mul_of_nonneg_left hf
      (show 0 ≤ 10*shortRatio^j by dsimp [shortRatio]; positivity)
    push_cast
    rw [pow_succ]
    nlinarith

theorem whole_terminal_Cauchy_chain_and_bulk_payment (m M0 : ℕ) (P d : ℝ)
    (hM : M0+39 ≤ 2*m) (hP : 0 ≤ P)
    (hTemplate : (41472/125:ℝ)*P ≤ base^39)
    (hRead : d*rho^m ≤ (324/125:ℝ)*base^M0*P) :
    (m:ℝ)*d ≤ (2:ℝ)^m := by
  have hb0 : (0:ℝ) < base := by norm_num [base]
  have hr0 : (0:ℝ) < rho := by norm_num [rho]
  have hpow := pow_le_pow_right₀ (show (1:ℝ) ≤ base by norm_num [base]) hM
  have hscale := mul_le_mul_of_nonneg_left hRead (pow_nonneg (le_of_lt hb0) 39)
  have hdegree := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (324/125:ℝ)*P by positivity)
  have hprod : base^M0*base^39=base^(M0+39) := (pow_add _ _ _).symm
  have hbaseId : base^2=(2:ℝ)*rho*ratio := by norm_num [base,rho,ratio]
  have htwo : base^(2*m)=(2:ℝ)^m*rho^m*ratio^m := by
    rw [pow_mul,hbaseId,mul_pow,mul_pow]
  have hread2 : rho^m*(base^39*d) ≤ rho^m*((324/125:ℝ)*P*ratio^m*(2:ℝ)^m) := by
    have hfull : (324/125:ℝ)*P*(base^M0*base^39) ≤ (324/125:ℝ)*P*base^(2*m) := by
      rw [hprod]
      exact hdegree
    rw [htwo] at hfull
    nlinarith
  have hclear := (mul_le_mul_iff_right₀ (pow_pos hr0 m)).mp hread2
  have hblock := whole_sixteen_power_block m
  have hfirst := mul_le_mul_of_nonneg_left hclear (show 0 ≤ (m:ℝ) by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hblock
    (show 0 ≤ (324/125:ℝ)*P*(2:ℝ)^m by positivity)
  have hthird := mul_le_mul_of_nonneg_right hTemplate (show 0 ≤ (2:ℝ)^m by positivity)
  have hfinal : base^39*((m:ℝ)*d) ≤ base^39*(2:ℝ)^m := by nlinarith
  exact (mul_le_mul_iff_right₀ (pow_pos hb0 39)).mp hfinal

#print axioms whole_large_capacity_offset_contraction
#print axioms whole_relative_capacity_envelope
#print axioms whole_sixteen_power_block
#print axioms whole_two_interval_weighted_coefficients
#print axioms whole_weighted_finite_convolution
#print axioms whole_fixed_terminal_product_budget
#print axioms whole_fixed_template_support_and_degree_guards
#print axioms whole_large_read_from_eighty
#print axioms whole_terminal_Cauchy_chain_and_bulk_payment
end
end FixedTerminalFourteenSlope
