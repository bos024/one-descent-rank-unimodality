import Mathlib

set_option maxHeartbeats 0
namespace FirstMissingRenewalEnvelope

theorem finite_ratio_chain (r : ℕ → ℝ) (N : ℕ)
    (h : ∀ i < N, r (i+1) ≤ r i) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ N) : r j ≤ r i := by
  have hh : ∀ j, i ≤ j → j ≤ N → r j ≤ r i := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      exact le_trans (h j (by omega)) (ih (by omega))
  exact hh j hij hj

theorem delayed_minor (a b c u v : ℝ)
    (hb : b=2*a-u) (hc : c=2*b-v) :
    b*b-a*c=a*v-b*u := by
  rw [hc,hb]
  ring

/-- Complete unbounded delayed-ratio induction, not a bounded computation. -/
theorem delayed_recurrence_lc (b : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hp : ∀ n, 0 < b n)
    (hbase : ∀ n < q, b (n+2)/b (n+1) ≤ b (n+1)/b n)
    (hrec : ∀ n, b (n+q+1)=2*b (n+q)-b n) :
    ∀ n, b (n+2)/b (n+1) ≤ b (n+1)/b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · exact hbase n hn
    · have hqn : q ≤ n := by omega
      let k := n-q
      have hk : k+q=n := by dsimp [k]; omega
      have hkn : k < n := by dsimp [k]; omega
      have hr := finite_ratio_chain (fun i => b (i+1)/b i) n
        (fun i hi => ih i hi) k n (by omega) (by omega)
      have hcross : b (n+1)*b k ≤ b (k+1)*b n :=
        (div_le_div_iff₀ (hp n) (hp k)).mp hr
      have hb : b (n+1)=2*b n-b k := by
        simpa only [hk] using hrec k
      have hc : b (n+2)=2*b (n+1)-b (k+1) := by
        have he : k+1+q=n+1 := by omega
        have he2 : k+1+q+1=n+2 := by omega
        simpa only [he,he2] using hrec (k+1)
      apply (div_le_div_iff₀ (hp (n+1)) (hp n)).mpr
      nlinarith [delayed_minor (b n) (b (n+1)) (b (n+2))
        (b k) (b (k+1)) hb hc]

theorem initial_dyadic_minor (q : ℕ) (hq : 1 ≤ q) :
    (2:ℝ)^q*(2:ℝ)^q-(2:ℝ)^(q-1)*((2:ℝ)^(q+1)-1)
      =(2:ℝ)^(q-1) := by
  have he : q=(q-1)+1 := by omega
  have hp : (2:ℝ)^q=(2:ℝ)^(q-1)*2 := by
    conv_lhs => rw [he,pow_succ]
  have hh : (2:ℝ)^(q+1)=(2:ℝ)^(q-1)*4 := by
    have he2 : q+1=(q-1)+2 := by omega
    rw [he2,pow_add]
    norm_num
  rw [hp,hh]
  ring

theorem normalized_shift_minor (p q u v : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : u/p ≤ v/q) : q*u ≤ p*v := by
  have hh := (div_le_div_iff₀ hp hq).mp h
  nlinarith

/-- Every nonnegative source loss is transported with the correct sign. -/
theorem finite_nonnegative_loss_transport {ι : Type*} (s : Finset ι)
    (p q b c : ℝ) (v x y : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hbase : p*c ≤ q*b)
    (hshift : ∀ i ∈ s, q*x i ≤ p*y i) :
    p*(c-∑ i ∈ s, v i*y i) ≤ q*(b-∑ i ∈ s, v i*x i) := by
  have hh : ∑ i ∈ s, v i*(q*x i) ≤ ∑ i ∈ s, v i*(p*y i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hshift i hi) (hv i hi)
  have hx : (∑ i ∈ s, v i*(q*x i))=q*(∑ i ∈ s, v i*x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hy : (∑ i ∈ s, v i*(p*y i))=p*(∑ i ∈ s, v i*y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hx,hy] at hh
  nlinarith

theorem positive_derivative_tail_density (a b p q : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ a) (hpq : p ≤ q) (hp : 0 ≤ p) :
    b*p ≤ a*q := by
  nlinarith

theorem source_identity_rearrangement (w conv v : ℝ)
    (h : v=1-w+conv) : w=1+conv-v := by linarith

theorem own_cumulative_source_counter :
    (14:ℤ)*29-9*43=19 ∧ (0:ℤ)<19 := by norm_num

#print axioms finite_ratio_chain
#print axioms delayed_minor
#print axioms delayed_recurrence_lc
#print axioms initial_dyadic_minor
#print axioms normalized_shift_minor
#print axioms finite_nonnegative_loss_transport
#print axioms positive_derivative_tail_density
#print axioms source_identity_rearrangement
#print axioms own_cumulative_source_counter
end FirstMissingRenewalEnvelope
