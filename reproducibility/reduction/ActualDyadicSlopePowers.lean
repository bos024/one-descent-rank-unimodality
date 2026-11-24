import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ActualDyadicSlopePowers
noncomputable section
def base : ℝ := 35/32
def ratio : ℝ := 6125/6144
def tail : ℝ := 3/2
def shortRatio : ℝ := 175/192
def triangle (n : ℕ) : ℕ := (n+1).choose 2

theorem whole_dyadic_power_block (m : ℕ) : (m:ℝ)*ratio^m ≤ 224 := by
  have h0 : (0:ℝ) ≤ ratio := by norm_num [ratio]
  have h1 : ratio ≤ 1 := by norm_num [ratio]
  have hblock : ratio^224 ≤ (1:ℝ)/2 := by norm_num [ratio]
  let a := m/224
  let r := m%224
  have hr : r < 224 := Nat.mod_lt _ (by norm_num)
  have hm : 224*a+r=m := by simpa [a,r,Nat.mul_comm] using Nat.div_add_mod m 224
  have hpow : ratio^m ≤ ((1:ℝ)/2)^a := by
    rw [←hm,pow_add,pow_mul]
    have hpa := pow_le_pow_left₀ (pow_nonneg h0 224) hblock a
    have hpr : ratio^r ≤ 1 := pow_le_one₀ h0 h1
    calc
      (ratio^224)^a*ratio^r ≤ ((1:ℝ)/2)^a*1 :=
        mul_le_mul hpa hpr (pow_nonneg h0 r) (by positivity)
      _ = ((1:ℝ)/2)^a := by ring
  have hm_nat : m ≤ 224*(a+1) := by omega
  have hm_real : (m:ℝ) ≤ 224*((a:ℝ)+1) := by exact_mod_cast hm_nat
  have hbin_nat : a+1 ≤ 2^a := Nat.succ_le_of_lt a.lt_two_pow_self
  have hbin : (a:ℝ)+1 ≤ (2:ℝ)^a := by exact_mod_cast hbin_nat
  have hhalf : ((a:ℝ)+1)*((1:ℝ)/2)^a ≤ 1 := by
    rw [one_div_pow,mul_one_div]
    exact (div_le_one (by positivity : (0:ℝ) < 2^a)).mpr hbin
  have hmul := mul_le_mul hm_real hpow (pow_nonneg h0 m)
    (show 0 ≤ 224*((a:ℝ)+1) by positivity)
  nlinarith

private theorem triangle_succ (n : ℕ) : triangle (n+1)=triangle n+(n+1) := by
  have h := Nat.choose_succ_succ' (n+1) 1
  simpa [triangle,Nat.choose_one_right,Nat.add_comm] using h

theorem whole_first_missing_twenty_triangle_budget (n : ℕ) (hn : 18 ≤ n) :
    2240*tail^n ≤ base^(triangle n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [tail,base,triangle,Nat.choose]
  | succ n hn ih =>
    have hb : (1:ℝ) ≤ base := by norm_num [base]
    have hsmall : tail ≤ base^5 := by norm_num [tail,base]
    have hbig : tail ≤ base^(n+1) :=
      hsmall.trans (pow_le_pow_right₀ hb (by omega))
    calc
      2240*tail^(n+1)=(2240*tail^n)*tail := by ring
      _ ≤ base^(triangle n)*base^(n+1) :=
        mul_le_mul ih hbig (by norm_num [tail]) (pow_nonneg (by norm_num [base]) _)
      _ = base^(triangle (n+1)) := by
        rw [triangle_succ]
        exact (pow_add base (triangle n) (n+1)).symm

theorem whole_large_read_exponential_budget (j : ℕ) (hj : 100 ≤ j) :
    10*((j:ℝ)+1)*shortRatio^j ≤ 1 := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [shortRatio]
  | succ j hj ih =>
    have hjR : (100:ℝ) ≤ j := by exact_mod_cast hj
    have hfactor : shortRatio*((j:ℝ)+2) ≤ (j:ℝ)+1 := by
      norm_num [shortRatio]
      nlinarith
    have hpow0 : (0:ℝ) ≤ shortRatio^j := pow_nonneg (by norm_num [shortRatio]) _
    push_cast
    calc
      10*((j:ℝ)+1+1)*shortRatio^(j+1)=
          (10*shortRatio^j)*(shortRatio*((j:ℝ)+2)) := by ring
      _ ≤ (10*shortRatio^j)*((j:ℝ)+1) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 10*((j:ℝ)+1)*shortRatio^j := by ring
      _ ≤ 1 := ih

theorem whole_bulk_Cauchy_to_signed_slope (m n : ℕ) (f d : ℝ)
    (hn : 18 ≤ n) (hd : d ≤ f)
    (hread : base^(triangle n)*f ≤ 10*tail^n*ratio^m*(2:ℝ)^m) :
    (m:ℝ)*d ≤ (2:ℝ)^m := by
  have hb0 : (0:ℝ) < base^(triangle n) := pow_pos (by norm_num [base]) _
  have hp0 : (0:ℝ) ≤ (2:ℝ)^m := by positivity
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hblock := whole_dyadic_power_block m
  have htriangle := whole_first_missing_twenty_triangle_budget n hn
  have hfirst := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ base^(triangle n)*(m:ℝ) by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hread hm0
  have hthird := mul_le_mul_of_nonneg_left hblock
    (show 0 ≤ 10*tail^n*(2:ℝ)^m by dsimp [tail]; positivity)
  have hfourth := mul_le_mul_of_nonneg_right htriangle hp0
  have htotal : base^(triangle n)*((m:ℝ)*d) ≤ base^(triangle n)*(2:ℝ)^m := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hb0).mp htotal

#print axioms whole_dyadic_power_block
#print axioms whole_first_missing_twenty_triangle_budget
#print axioms whole_large_read_exponential_budget
#print axioms whole_bulk_Cauchy_to_signed_slope
end
end ActualDyadicSlopePowers
