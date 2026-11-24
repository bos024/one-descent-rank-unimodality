import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

namespace QuantitativeTiltStrongOneJump

theorem entire_kernel_row (a : ℝ) (T : ℕ → ℝ) (h0 : T 0=1)
    (hs : ∀ n,T (n+1)=a*T n+2*(1-a)+(n:ℝ)*(1-a)^2) :
    ∀ n,T n=1+(n:ℝ)*(1-a) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [hs,ih]; push_cast; ring

theorem quantitative_normalized_tilt (a c mu k : ℝ)
    (ha0 : 0≤a) (ha1 : a≤1) (hc0 : 0≤c) (hc1 : c≤1)
    (hmu : 1 ≤ mu) (hk : 0≤k) :
    a^2*c ≤ (2*(1-a)+(k-1)*(1-a)^2)
      +c*(1+k*(1-a)-(2*(1-a)+(k-1)*(1-a)^2))
      +(a^2-1)*(1+k*(1-mu)) := by
  have h1 : 0≤(1-c)*(1-a)+c+(1+a)*(mu-1) := by positivity
  have h2 := mul_nonneg (mul_nonneg hk (show 0≤1-a by linarith)) h1
  have hid : (2*(1-a)+(k-1)*(1-a)^2)
      +c*(1+k*(1-a)-(2*(1-a)+(k-1)*(1-a)^2))
      +(a^2-1)*(1+k*(1-mu))-a^2*c
      =k*(1-a)*((1-c)*(1-a)+c+(1+a)*(mu-1)) := by ring
  nlinarith

theorem finite_weighted_reference_margin (I : Finset ℕ) (w H : ℕ → ℝ)
    (c : ℝ) (hzero : 0∈I) (hw : ∀ i∈I,0≤w i)
    (hH : ∀ i∈I,c≤H i) (hH0 : H 0=1) :
    w 0+c*((∑ i ∈ I,w i)-w 0)≤∑ i ∈ I,w i*H i := by
  have hh : ∀ i∈I,0≤w i*(H i-c) := by
    intro i hi
    exact mul_nonneg (hw i hi) (by linarith [hH i hi])
  have hsingle : w 0*(H 0-c)≤∑ i ∈ I,w i*(H i-c) :=
    Finset.single_le_sum hh hzero
  rw [hH0] at hsingle
  have hid : (∑ i ∈ I,w i*(H i-c))=(∑ i ∈ I,w i*H i)-c*(∑ i ∈ I,w i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid] at hsingle
  nlinarith

theorem additive_margin_LR_transfer (X Y A B mu c : ℝ)
    (hB : 0<B) (hY : B≤Y) (hc : 0≤c)
    (hLR : A*Y≤X*B) (hgap : c≤A-mu*B) :
    c≤X-mu*Y := by
  have h1 := mul_nonneg (show 0≤A-mu*B-c by linarith) (show 0≤Y by linarith)
  have h2 := mul_nonneg hc (show 0≤Y-B by linarith)
  nlinarith

theorem weighted_negative_coefficient (m b w : ℝ)
    (hb : 0≤b) (hm : -b ≤ m) (hw0 : 0≤w) (hw1 : w≤1) :
    -b ≤ m*w := by
  have h1 := mul_nonneg (show 0 ≤ m+b by linarith) hw0
  have h2 := mul_nonneg hb (show 0≤1-w by linarith)
  nlinarith

theorem all_capacity_polynomial_payment (I : Finset ℕ)
    (m b w : ℕ → ℝ) (X Y Z a last : ℝ)
    (_ha0 : 0≤a) (ha1 : a≤1) (hY : 1≤Y) (hZ : 0≤Z)
    (hfib : 2*X-3*Y=Z) (hsum : (∑ i ∈ I,b i)=Y-2)
    (hb : ∀ i∈I,0≤b i) (hm : ∀ i∈I,-b i ≤ m i)
    (hw0 : ∀ i∈I,0≤w i) (hw1 : ∀ i∈I,w i≤1)
    (hlast : 0≤last) :
    4≤2*X+(2-2*Y)*a+(∑ i ∈ I,m i*w i)+last := by
  have hs : -(∑ i ∈ I,b i)≤∑ i ∈ I,m i*w i := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact weighted_negative_coefficient (m i) (b i) (w i) (hb i hi) (hm i hi) (hw0 i hi) (hw1 i hi)
  have h1 := mul_nonneg (show 0≤2*Y-2 by linarith) (show 0≤1-a by linarith)
  rw [hsum] at hs
  nlinarith

theorem fibonacci_middle_budget (f : ℕ → ℝ) (h3 : f 3=2)
    (hs : ∀ n,f (n+2)=f (n+1)+f n) :
    ∀ n,(∑ j ∈ Finset.range n,f (j+2))=f (n+3)-2 := by
  intro n
  induction n with
  | zero => simp [h3]
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      have hh : f (n+4)=f (n+3)+f (n+2) := by simpa only [Nat.add_assoc] using hs (n+2)
      rw [show n+1+3=n+4 by omega]
      linarith

theorem fibonacci_linear_budget (f : ℕ → ℝ)
    (hs : ∀ n,f (n+2)=f (n+1)+f n) (n : ℕ) :
    2*f (n+4)-3*f (n+3)=f n := by
  have h0 := hs n
  have h1 := hs (n+1)
  have h2 := hs (n+2)
  simp only [Nat.add_assoc] at h1 h2
  nlinarith

theorem capacity_three_tilt_seed (a : ℝ) :
    2*(2+2*a)-a*2*2=4 := by ring

#print axioms entire_kernel_row
#print axioms quantitative_normalized_tilt
#print axioms finite_weighted_reference_margin
#print axioms additive_margin_LR_transfer
#print axioms weighted_negative_coefficient
#print axioms all_capacity_polynomial_payment
#print axioms fibonacci_middle_budget
#print axioms fibonacci_linear_budget
#print axioms capacity_three_tilt_seed

end QuantitativeTiltStrongOneJump

