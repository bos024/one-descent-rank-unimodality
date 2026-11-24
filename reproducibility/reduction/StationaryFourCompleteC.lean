import Mathlib
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace StationaryFourCompleteC

theorem exact_quartic_seven_step_minor_recurrence (a b c d : ℝ) :
    let e := a+b+c+d
    let f := b+c+d+e
    let g := c+d+e+f
    let h := d+e+f+g
    let i := e+f+g+h
    let j := f+g+h+i
    i^2-h*j = -(b^2-a*c)+2*(c^2-b*d)-3*(d^2-c*e)+
      4*(e^2-d*f)-(g^2-f*h) := by
  dsimp
  ring

theorem seven_step_growth_budget (k0 k1 k2 k3 k4 k5 k6 k7 : ℝ)
    (h7 : 0 ≤ k7) (h0 : 9*k0 ≤ 5*k1) (h1 : 9*k1 ≤ 5*k2)
    (h2 : 9*k2 ≤ 5*k3) (h3 : 9*k3 ≤ 5*k4) (h4 : 9*k4 ≤ 5*k5)
    (h5 : 9*k5 ≤ 5*k6) (h6 : 9*k6 ≤ 5*k7) :
    k0+2*k1+3*k2+4*k3+k5 ≤ k7 := by linarith

theorem whole_seven_step_absolute_majorant (M K : ℕ → ℝ)
    (hrec : ∀ n,M (n+7)= -M n+2*M (n+1)-3*M (n+2)+4*M (n+3)-M (n+5))
    (hpos : ∀ n,0 ≤ K n) (hgrow : ∀ n,9*K n ≤ 5*K (n+1))
    (hbase : ∀ n,n<7 → |M n| ≤ K n) : ∀ n,|M n| ≤ K n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<7
    · exact hbase n hn
    · let m := n-7
      have he : n=m+7 := by dsimp [m]; omega
      have h0 := abs_le.mp (ih m (by dsimp [m]; omega))
      have h1 := abs_le.mp (ih (m+1) (by dsimp [m]; omega))
      have h2 := abs_le.mp (ih (m+2) (by dsimp [m]; omega))
      have h3 := abs_le.mp (ih (m+3) (by dsimp [m]; omega))
      have h5 := abs_le.mp (ih (m+5) (by dsimp [m]; omega))
      have hbudget := seven_step_growth_budget (K m) (K (m+1)) (K (m+2))
        (K (m+3)) (K (m+4)) (K (m+5)) (K (m+6)) (K (m+7))
        (hpos _) (hgrow m) (by simpa [Nat.add_assoc] using hgrow (m+1))
        (by simpa [Nat.add_assoc] using hgrow (m+2))
        (by simpa [Nat.add_assoc] using hgrow (m+3))
        (by simpa [Nat.add_assoc] using hgrow (m+4))
        (by simpa [Nat.add_assoc] using hgrow (m+5))
        (by simpa [Nat.add_assoc] using hgrow (m+6))
      rw [he,hrec m]
      apply abs_le.mpr
      constructor <;> linarith

theorem three_actual_left_ordinary_minors (a B C D t0 t1 t2 t3 t4 : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h0 : 0 ≤ t0) (h1 : 0 ≤ t1) (h2 : 0 ≤ t2)
    (hg0 : t1 ≤ 2*t0) (hg1 : t2 ≤ 2*t1) (hg2 : t3 ≤ 2*t2)
    (hm0 : -t0 ≤ t1^2-t0*t2) (hm1 : -t1 ≤ t2^2-t1*t3)
    (hm2 : -t2 ≤ t3^2-t2*t4)
    (hb0 : 0 ≤ B-4*a-1) (hb1 : 0 ≤ C-4*B-1) (hb2 : 0 ≤ D-4*C-1)
    (hnext0 : C ≤ t3) (hnext1 : D ≤ t4) :
    0 ≤ (t1-a)^2-t0*(t2-B) ∧
    0 ≤ (t2-B)^2-(t1-a)*(t3-C) ∧
    0 ≤ (t3-C)^2-(t2-B)*(t4-D) := by
  have p0 := mul_nonneg h0 hb0
  have p1 := mul_nonneg h1 hb1
  have p2 := mul_nonneg h2 hb2
  have q0 := mul_nonneg ha (show 0 ≤ 2*t0-t1 by linarith)
  have q1 := mul_nonneg hB (show 0 ≤ 2*t1-t2 by linarith)
  have q2 := mul_nonneg hC (show 0 ≤ 2*t2-t3 by linarith)
  have q3 := mul_nonneg ha (show 0 ≤ t3-C by linarith)
  have q4 := mul_nonneg hB (show 0 ≤ t4-D by linarith)
  constructor
  · nlinarith only [hm0,p0,q0,sq_nonneg a]
  · constructor
    · nlinarith only [hm1,p1,q1,q3,sq_nonneg B]
    · nlinarith only [hm2,p2,q2,q4,sq_nonneg C]

theorem all_binary_seed_three_startup_budgets (r a b c d : ℝ)
    (hr : 8 ≤ r) (ha : 1 ≤ a) (hb : 2*a ≤ b)
    (hc : 4*a-1 ≤ c) (hd : 8*a-3 ≤ d) :
    let B := a*r+b
    let C := a*r*(r+1)/2+b*r+c
    let D := a*r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d
    0 ≤ B-4*a-1 ∧ 0 ≤ C-4*B-1 ∧ 0 ≤ D-4*C-1 := by
  dsimp
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h01 := mul_nonneg ha0 (show 0 ≤ r-4 by linarith)
  have h02 := mul_nonneg ha0 (show 0 ≤ r*(r-7)/2 by nlinarith)
  have h03 := mul_nonneg hb0 (show 0 ≤ r-4 by linarith)
  have hfour : 0 ≤ a*r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d-
      4*(a*r*(r+1)/2+b*r+c)-1 := by
    have hid : a*r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d-
        4*(a*r*(r+1)/2+b*r+c)-1 =
        a*(r-8)*(r+2)*(r+3)/6+(a-1)*r+
        (b-2*a)*r*(r-7)/2+(c-4*a+1)*(r-4)+(d-8*a+3) := by ring
    rw [hid]
    have hr8 : 0 ≤ r-8 := by linarith
    have hr7 : 0 ≤ r-7 := by linarith
    have hr4 : 0 ≤ r-4 := by linarith
    have hr0 : 0 ≤ r := by linarith
    have ha1 : 0 ≤ a-1 := by linarith
    have hb2 : 0 ≤ b-2*a := by linarith
    have hc4 : 0 ≤ c-4*a+1 := by linarith
    have hd8 : 0 ≤ d-8*a+3 := by linarith
    positivity
  exact ⟨by nlinarith only [h01,hb,ha],by nlinarith only [h02,h03,hc,ha], hfour⟩

theorem reference_three_startup_budgets (r b c d : ℝ)
    (hr : 9 ≤ r) (hb : 1 ≤ b) (hc : 2 ≤ c) (hd : 4 ≤ d) :
    let B := r+b
    let C := r*(r+1)/2+b*r+c
    let D := r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d
    0 ≤ B-5 ∧ 0 ≤ C-4*B-1 ∧ 0 ≤ D-4*C-1 := by
  dsimp
  have h0 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r-7 by linarith)
  have h1 := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ r-4 by linarith)
  have hfour : 0 ≤ r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d-
      4*(r*(r+1)/2+b*r+c)-1 := by
    have hid : r*(r+1)*(r+2)/6+b*r*(r+1)/2+c*r+d-
        4*(r*(r+1)/2+b*r+c)-1 =
        7+(r-9)*(r^2+3*r+8)/6+(b-1)*r*(r-7)/2+
        (c-2)*(r-4)+(d-4) := by ring
    rw [hid]
    have hr9 : 0 ≤ r-9 := by linarith
    have hr7 : 0 ≤ r-7 := by linarith
    have hr4 : 0 ≤ r-4 := by linarith
    have hr0 : 0 ≤ r := by linarith
    have hb1 : 0 ≤ b-1 := by linarith
    have hc2 : 0 ≤ c-2 := by linarith
    have hd4 : 0 ≤ d-4 := by linarith
    positivity
  exact ⟨by linarith only [hr,hb],by nlinarith only [h0,h1,hc],hfour⟩

theorem analytic_first_degree_crossing_and_padding_clamp (u : ℕ) :
    (21 ≤ u → let r := u/3+1
      8 ≤ r ∧ 5 ≤ u ∧ u<3*r ∧ 3*r-3 ≤ u ∧
      4*r-1 ≤ u+r+2 ∧ r+3 ≤ 4*r-3) ∧
    (∀ alpha n, (u+24)/2 ≤ alpha → n ≤ (3*u+40)/2 →
      n<alpha+u+8+1 ∧ n<(u+24)/2+u+8+1) := by
  constructor
  · intro hu
    dsimp
    omega
  · intro alpha n ha hn
    omega

theorem quartic_Fibonacci_tail_norm_and_minor (u v a b : ℝ) :
    (2*u-v)^2-(2*u-v)*(3*v-u)-(3*v-u)^2=5*(u^2-u*v-v^2) ∧
    (u*b+v*a)^2-(u*a+v*(b-a))*(u*(a+b)+v*b)=
      (u^2-u*v-v^2)*(b^2-a*b-a^2) := by constructor <;> ring

theorem entire_terminal_power_potential (a : ℝ) (ha : 0 ≤ a) (hA : a ≤ 3/5) :
    ∀ r : ℕ,4 ≤ r → ((r:ℝ)+2)*a^r ≤ 1 := by
  have hbase : (6:ℝ)*a^4 ≤ 1 := by
    have hh : a^4 ≤ (3/5:ℝ)^4 := pow_le_pow_left₀ ha hA 4
    nlinarith only [hh]
  have hall : ∀ k : ℕ,(((4+k:ℕ):ℝ)+2)*a^(4+k) ≤ 1 := by
    intro k
    induction k with
    | zero =>
        convert hbase using 1
        norm_num
    | succ k ih =>
        have hp : 0 ≤ a^(4+k) := pow_nonneg ha _
        have ha2 : (((4+k:ℕ):ℝ)+3)*a ≤ ((4+k:ℕ):ℝ)+2 := by
          have hh := mul_nonneg (show 0 ≤ ((4+k:ℕ):ℝ)+3 by positivity)
            (show 0 ≤ (3/5:ℝ)-a by linarith)
          have hk : 0 ≤ (k:ℝ) := by positivity
          push_cast at *
          nlinarith
        have hh := mul_le_mul_of_nonneg_right ha2 hp
        have hid : ((((4+(k+1):ℕ):ℝ)+2)*a^(4+(k+1)))=
            ((((4+k:ℕ):ℝ)+3)*a)*a^(4+k) := by
          simp only [Nat.cast_add,Nat.cast_one]
          ring
        change (((4+(k+1):ℕ):ℝ)+2)*a^(4+(k+1)) ≤ 1
        rw [hid]
        exact le_trans hh ih
  intro r hr
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hr
  rw [hk]
  exact hall k

theorem both_terminal_ordinary_inverse_corners (p r tau : ℝ)
    (hp : 1 ≤ p) (hP : p ≤ 2) (hr : 5 ≤ r) (ht : 0 ≤ tau)
    (hpotential : (r+2)*tau ≤ 1) :
    let v := p*(1-tau)
    let w := p*(r-p+p*tau)
    let x := p*(r*(r+1)/2-p*r+p^2-p^2*tau)
    0 ≤ v^2-w*tau ∧ 0 ≤ w^2-x*v := by
  dsimp
  have hp0 : 0 ≤ p := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hterm : 0 ≤ p-(r+p)*tau := by
    have hh := mul_nonneg (show 0 ≤ 2-p by linarith) ht
    linarith
  have h0 := mul_nonneg hp0 hterm
  have h1 : 0 ≤ r*(r-2*p-1)/2 := by
    have hh := mul_nonneg hr0 (show 0 ≤ r-2*p-1 by linarith)
    nlinarith
  have h2 : 0 ≤ (r*(r+1)/2+p*r)*tau := by positivity
  have h3 := mul_nonneg (sq_nonneg p) (add_nonneg h1 h2)
  constructor
  · nlinarith only [h0]
  · nlinarith only [h3]

def cseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 1
  | n+1 => (z+z^2+z^3+z^4)*cseq z n+(1-z-z^2)

def jseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 0
  | n+1 => (z+z^2+z^3+z^4)*jseq z n+1-(z^2+2)*(2-z)^n

theorem whole_quartic_reference_tail_polynomial_identity {R : Type*} [CommRing R]
    (z : R) : ∀ r : ℕ,cseq z r=(2-z)^r+(1-z-z^2)*jseq z r := by
  intro r
  induction r with
  | zero => simp [cseq,jseq]
  | succ r ih =>
      simp only [cseq,jseq,ih,pow_succ]
      ring

#print axioms exact_quartic_seven_step_minor_recurrence
#print axioms seven_step_growth_budget
#print axioms whole_seven_step_absolute_majorant
#print axioms three_actual_left_ordinary_minors
#print axioms all_binary_seed_three_startup_budgets
#print axioms reference_three_startup_budgets
#print axioms analytic_first_degree_crossing_and_padding_clamp
#print axioms quartic_Fibonacci_tail_norm_and_minor
#print axioms entire_terminal_power_potential
#print axioms both_terminal_ordinary_inverse_corners
#print axioms whole_quartic_reference_tail_polynomial_identity
end StationaryFourCompleteC
