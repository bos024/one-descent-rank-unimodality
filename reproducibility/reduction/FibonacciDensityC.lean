import RegularizedFibonacciEnvelope

set_option maxHeartbeats 0
namespace FibonacciDensityC
open RegularizedFibonacciEnvelope

theorem power_gap_nonnegative (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    0 ≤ 1-(j+1:ℝ)*a^j+(j:ℝ)*a^(j+1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hp := mul_nonneg (mul_nonneg (show 0 ≤ (j+1:ℝ) by positivity)
      (pow_nonneg ha j)) (sq_nonneg (1-a))
    simp only [Nat.cast_add,Nat.cast_one,pow_succ] at *
    nlinarith only [ih,hp]

theorem adjacent_power_gap_order (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    (j:ℝ)*(1-a^(j+1)) ≤ (j+1:ℝ)*(1-a^j) := by
  have hs := power_gap_nonnegative a ha j
  nlinarith only [hs]

theorem paired_coefficient_payment (a A B : ℝ) (j : ℕ)
    (ha : 0 ≤ a) (hle : a ≤ 1) (hj : 1 ≤ j) (hB : 0 ≤ B)
    (hcoeff : (j+1:ℝ)*B ≤ (j:ℝ)*A) :
    -A+B ≤ -A*a^j+B*a^(j+1) := by
  have hpow : a^j ≤ 1 := pow_le_one₀ ha hle
  have h1 := mul_nonneg (sub_nonneg.mpr hcoeff) (sub_nonneg.mpr hpow)
  have h2 := mul_nonneg hB (power_gap_nonnegative a ha j)
  have hjpos : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hs : 0 ≤ (j:ℝ)*(A*(1-a^j)-B*(1-a^(j+1))) := by
    nlinarith only [h1,h2]
  have ht := (mul_nonneg_iff_of_pos_left hjpos).mp hs
  nlinarith only [ht]

theorem alternating_polynomial_payment (a c0 c1 tail : ℝ) (s : Finset ℕ)
    (A B : ℕ → ℝ) (t : ℕ) (ha : 0 ≤ a) (hle : a ≤ 1)
    (hc1 : c1 ≤ 0) (htail : tail ≤ 0)
    (hj : ∀ j ∈ s, 1 ≤ j) (hB : ∀ j ∈ s, 0 ≤ B j)
    (hcoeff : ∀ j ∈ s, (j+1:ℝ)*B j ≤ (j:ℝ)*A j) :
    c0+c1+(∑ j ∈ s, (-A j+B j))+tail ≤
      c0+c1*a+(∑ j ∈ s, (-A j*a^j+B j*a^(j+1)))+tail*a^t := by
  have hs := Finset.sum_le_sum (fun j hjm =>
    paired_coefficient_payment a (A j) (B j) j ha hle (hj j hjm)
      (hB j hjm) (hcoeff j hjm))
  have hlin := mul_le_mul_of_nonpos_left hle hc1
  have hpow : a^t ≤ 1 := pow_le_one₀ ha hle
  have ht := mul_le_mul_of_nonpos_left hpow htail
  nlinarith only [hs,hlin,ht]

theorem Fibonacci_determinant (p j : ℕ) :
    fi (p+j+1)*fi (j+2)-fi (p+j+2)*fi (j+1)=(-1:ℤ)^(j+1)*fi p := by
  induction j with
  | zero =>
    simp only [Nat.add_zero]
    rw [show fi 2=1 by norm_num [fi],show fi 1=1 by norm_num [fi],fi_rec p]
    ring
  | succ j ih =>
    have he : p+(j+1)+1=p+j+2 := by omega
    have he2 : p+(j+1)+2=p+j+3 := by omega
    have he3 : j+1+2=j+3 := by omega
    rw [he,he2,he3]
    have hr1 : fi (p+j+3)=fi (p+j+1)+fi (p+j+2) := by
      simpa [Nat.add_assoc] using fi_rec (p+j+1)
    have hr2 : fi (j+3)=fi (j+1)+fi (j+2) := by
      simpa [Nat.add_assoc] using fi_rec (j+1)
    have hsign : (-1:ℤ)^(j+1+1)= -((-1:ℤ)^(j+1)) := by
      rw [pow_succ]; ring
    rw [hsign]
    have hid : fi (p+j+2)*fi (j+3)-fi (p+j+3)*fi (j+2)=
      -(fi (p+j+1)*fi (j+2)-fi (p+j+2)*fi (j+1)) := by
      rw [hr1,hr2]
      ring
    rw [hid,ih]
    ring

theorem Fibonacci_three_halves (n : ℕ) (hn : 3 ≤ n) :
    3*fi n ≤ 2*fi (n+1) := by
  have hr1 := fi_rec (n-1)
  have hr2 := fi_rec (n-2)
  have he1 : n-1+2=n+1 := by omega
  have he2 : n-2+2=n := by omega
  have he3 : n-2+1=n-1 := by omega
  rw [he1] at hr1
  rw [show n-1+1=n by omega] at hr1
  rw [he2,he3] at hr2
  have hm : fi (n-2) ≤ fi (n-1) := by
    unfold fi
    exact_mod_cast (Nat.fib_mono (show n-2 ≤ n-1 by omega))
  linarith

theorem paired_Fibonacci_coefficients (j m e : ℕ) (hj : 2 ≤ j) (hm : 4 ≤ m) :
    ((j+1:ℕ):ℤ)*((m:ℤ)-3)*fi (m-1+e) ≤
      (j:ℤ)*((m:ℤ)-2)*fi (m+e) := by
  have hf := Fibonacci_three_halves (m-1+e) (by omega)
  have he : m-1+e+1=m+e := by omega
  rw [he] at hf
  have hp := positive_fibonacci (m-1+e) (by omega)
  have hs := mul_nonneg (show 0 ≤ (m:ℤ)-3 by omega) (sub_nonneg.mpr hf)
  have hf2 : 3*(((m:ℤ)-3)*fi (m-1+e)) ≤
      2*(((m:ℤ)-2)*fi (m+e)) := by
    have hpos := positive_fibonacci (m+e) (by omega)
    nlinarith only [hs,hpos]
  have hb : 0 ≤ ((m:ℤ)-3)*fi (m-1+e) := mul_nonneg (by omega) (by omega)
  have hp2 := mul_nonneg (show 0 ≤ (j:ℤ) by omega) (sub_nonneg.mpr hf2)
  have hp3 := mul_nonneg (show 0 ≤ (j:ℤ)-2 by omega) hb
  push_cast
  nlinarith only [hp2,hp3]

theorem first_Fibonacci_endpoint (k : ℕ) :
    fi (k+1)*(fi (k+3)-1)-fi (k+2)*(fi (k+2)-1)=
      fi k-(-1:ℤ)^(k+1) := by
  have hc := cassini (k+1)
  have hr := fi_rec k
  nlinarith only [hc,hr]

theorem second_Fibonacci_endpoint (k : ℕ) :
    fi (k+2)*(fi (k+3)-1)-fi (k+3)*(fi (k+2)-1)=fi (k+1) := by
  have hr := fi_rec (k+1)
  nlinarith only [hr]

theorem two_seed_Fibonacci_nonnegative (H : ℕ → ℝ)
    (h0 : 0 ≤ H 0) (h1 : 0 ≤ H 1)
    (hrec : ∀ n, H (n+2)=H n+H (n+1)) : ∀ n, 0 ≤ H n := by
  have hp : ∀ n, 0 ≤ H n ∧ 0 ≤ H (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih =>
      constructor
      · exact ih.2
      · have hr := hrec n
        have he : n+1+1=n+2 := by omega
        rw [he,hr]
        exact add_nonneg ih.1 ih.2
  intro n
  exact (hp n).1

theorem cumulative_LR_adjacent (x y : ℕ → ℝ) (k : ℕ)
    (hLR : ∀ j, j < k → x j*y k ≤ x k*y j) :
    (∑ j ∈ Finset.range k, x j)*(∑ j ∈ Finset.range (k+1), y j) ≤
      (∑ j ∈ Finset.range (k+1), x j)*(∑ j ∈ Finset.range k, y j) := by
  have hs : 0 ≤ ∑ j ∈ Finset.range k, (x k*y j-y k*x j) := by
    apply Finset.sum_nonneg
    intro j hj
    have hh := hLR j (Finset.mem_range.mp hj)
    nlinarith only [hh]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum] at hs
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  nlinarith only [hs]

theorem ratio_chain_on_prefix (x y : ℕ → ℝ) (K : ℕ)
    (hy : ∀ n, n ≤ K → 0 < y n)
    (hadj : ∀ n, n+1 ≤ K → x n*y (n+1) ≤ x (n+1)*y n) :
    ∀ u r, u ≤ r → r ≤ K → x u*y r ≤ x r*y u := by
  intro u r hur
  induction r, hur using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ r hr ih =>
    intro hrK
    have h1 := mul_le_mul_of_nonneg_right (ih (by omega)) (le_of_lt (hy (r+1) hrK))
    have h2 := mul_le_mul_of_nonneg_right (hadj r hrK) (le_of_lt (hy u (by omega)))
    apply (mul_le_mul_iff_right₀ (hy r (by omega))).mp
    nlinarith only [h1,h2]

theorem model_C_transfer (G Gp H Hp D Dp a r s : ℝ)
    (hGp : 0 < Gp) (hHp : 0 < Hp) (hDp : 0 < Dp) (hr : 0 < r)
    (hLR : Gp*H ≤ G*Hp) (hmodel : a*s*Hp ≤ r*H)
    (hratio : r*D=a*s*Dp) : Gp*D ≤ G*Dp := by
  have h1 := mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hLR)
  have h2 := mul_nonneg (le_of_lt hGp) (sub_nonneg.mpr hmodel)
  have h3 : 0 ≤ Hp*(r*G-a*s*Gp) := by nlinarith only [h1,h2]
  have h4 := (mul_nonneg_iff_of_pos_left hHp).mp h3
  have h5 := mul_nonneg (le_of_lt hDp) h4
  have he := congrArg (fun x : ℝ => Gp*x) hratio
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith only [h5,he]

#print axioms power_gap_nonnegative
#print axioms adjacent_power_gap_order
#print axioms paired_coefficient_payment
#print axioms alternating_polynomial_payment
#print axioms Fibonacci_determinant
#print axioms Fibonacci_three_halves
#print axioms paired_Fibonacci_coefficients
#print axioms first_Fibonacci_endpoint
#print axioms second_Fibonacci_endpoint
#print axioms two_seed_Fibonacci_nonnegative
#print axioms cumulative_LR_adjacent
#print axioms ratio_chain_on_prefix
#print axioms model_C_transfer
end FibonacciDensityC
