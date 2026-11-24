import Mathlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace AllBinaryTernaryCompleteC

theorem universal_binary_seed_two_ordinary_entrances (r a b c T U V W : ℝ)
    (hr : 7 ≤ r) (ha : 1 ≤ a) (hb : 2 ≤ b) (hc : 5 ≤ c)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hUV : U ≤ 2*T) (hVW : V ≤ 2*U)
    (hM0 : -T ≤ U^2-T*V) (hM1 : -U ≤ V^2-U*W)
    (hnext : a*r*(r+1)/2+b*r+c ≤ W) :
    let B := a*r+b
    let C := a*r*(r+1)/2+b*r+c
    0 ≤ (U-a)^2-T*(V-B) ∧ 0 ≤ (V-B)^2-(U-a)*(W-C) := by
  dsimp
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hbudget0 : 0 ≤ a*r+b-4*a-1 := by
    have h := mul_nonneg ha0 (show 0 ≤ r-4 by linarith)
    nlinarith
  have hbudget1 : 0 ≤ a*r*(r+1)/2+b*r+c-4*(a*r+b)-1 := by
    have hid : a*r*(r+1)/2+b*r+c-4*(a*r+b)-1
      =a*(r*(r-7)/2)+b*(r-4)+(c-1) := by ring
    rw [hid]
    have h1 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r-7 by linarith)
    have h2 := mul_nonneg ha0 (show 0 ≤ r*(r-7)/2 by nlinarith)
    have h3 := mul_nonneg hb0 (show 0 ≤ r-4 by linarith)
    linarith
  have h0 := mul_nonneg hT hbudget0
  have h1 := mul_nonneg ha0 (show 0 ≤ 2*T-U by linarith)
  have h2 := mul_nonneg hU hbudget1
  have h3 := mul_nonneg (show 0 ≤ a*r+b by nlinarith) (show 0 ≤ 2*U-V by linarith)
  have h4 := mul_nonneg ha0 (show 0 ≤ W-(a*r*(r+1)/2+b*r+c) by linarith)
  have hid : (V-(a*r+b))^2-(U-a)*(W-(a*r*(r+1)/2+b*r+c))
    =(V^2-U*W)-2*(a*r+b)*V+(a*r+b)^2+U*(a*r*(r+1)/2+b*r+c)+a*(W-(a*r*(r+1)/2+b*r+c)) := by ring
  constructor
  · nlinarith [sq_nonneg a]
  · nlinarith [sq_nonneg (a*r+b)]

theorem unbounded_first_degree_crossing_seed_guards (u : ℕ) (hu : 10 ≤ u) :
    let r := u/2+1
    6 ≤ r ∧ 5 ≤ u ∧ u<2*r ∧ 2*r-2 ≤ u ∧
      3*r-1<u+r+2 ∧ r+3 ≤ 3*r-2 := by omega

theorem exact_small_binary_fixed_six_padding_clamp (u alpha n : ℕ)
    (_hu : 1 ≤ u) (_hU : u ≤ 9) (ha : 6+u/2 ≤ alpha)
    (hn : n ≤ (3*u+24)/2) :
    n<6+u+alpha+1 ∧ n<6+u+(6+u/2)+1 := by omega

theorem deficit_stationary_three_induction (P : ℕ → ℕ → Prop)
    (seed_large : ∀ u,10 ≤ u → P u (u/2+1))
    (seed_small : ∀ u,1 ≤ u → u ≤ 9 → P u 6)
    (step : ∀ u r,1 ≤ u → 6 ≤ r → P u r → P u (r+1)) :
    ∀ u r,1 ≤ u → 6 ≤ r → u<2*r → P u r := by
  intro u r hu hr hdef
  by_cases hlarge : 10 ≤ u
  · have hstart := seed_large u hlarge
    have h0 : 6 ≤ u/2+1 := by omega
    have hlow : u/2+1 ≤ r := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hlow
    rw [hk]
    clear hk
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
        have h := step u (u/2+1+k) hu (by omega) ih
        simpa [Nat.add_assoc] using h
  · have hsmall : u ≤ 9 := by omega
    have hstart := seed_small u hu hsmall
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hr
    rw [hk]
    clear hk
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
        have h := step u (6+k) hu (by omega) ih
        simpa [Nat.add_assoc] using h

theorem exhaustive_all_count_C_union (u r : ℕ) :
    u=0 ∨ r ≤ 5 ∨ (1 ≤ u ∧ 6 ≤ r ∧ u<2*r) ∨ max 0 (2*r-3) ≤ u := by omega

theorem sharp_surplus_boundary_read_guards (u r : ℕ) (hr : 6 ≤ r) :
    (u=2*r → u+r+1=3*r+1 ∧ u+r+2=3*r+2) ∧
    (2*r+1 ≤ u → 3*r+2<u+r+2 ∧ r+3 ≤ 3*r+1) := by omega

def cseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 1
  | n+1 => (z+z^2+z^3)*cseq z n+(1-z-z^2)
def jseq {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 0
  | n+1 => 1+(z+z^2+z^3)*jseq z n-z*(2*z)^n

theorem whole_reference_binary_tail_polynomial_identity {R : Type*} [CommRing R]
    (z : R) : ∀ r : ℕ,cseq z r=(2*z)^r+(1-z-z^2)*jseq z r := by
  intro r
  induction r with
  | zero => simp [cseq,jseq]
  | succ r ih =>
      simp only [cseq,jseq,ih,pow_succ]
      ring

theorem whole_even_fibonacci_Cassini (f : ℕ → ℝ)
    (h0 : f 0=0) (h1 : f 1=1) (hr : ∀ n,f (n+2)=f n+f (n+1)) :
    ∀ r : ℕ,(f (2*r+2))^2-f (2*r+1)*f (2*r+3)= -1 := by
  let M : ℕ → ℝ := fun n => (f (n+1))^2-f n*f (n+2)
  have hm : ∀ n,M (n+1)= -M n := by
    intro n
    dsimp [M]
    have h2 := hr n
    have h3 : f (n+3)=f (n+1)+f (n+2) := by simpa [Nat.add_assoc] using hr (n+1)
    simp only [show n+1+1=n+2 by omega,show n+1+2=n+3 by omega,h3,h2]
    ring
  have hc : ∀ n,M n=(-1:ℝ)^n := by
    intro n
    induction n with
    | zero => simp [M,h0,h1]
    | succ n ih => rw [hm,ih,pow_succ];ring
  intro r
  have h := hc (2*r+1)
  norm_num [pow_add,pow_mul] at h
  simpa [M,show 2*r+1+1=2*r+2 by omega,show 2*r+1+2=2*r+3 by omega] using h

#print axioms universal_binary_seed_two_ordinary_entrances
#print axioms unbounded_first_degree_crossing_seed_guards
#print axioms exact_small_binary_fixed_six_padding_clamp
#print axioms deficit_stationary_three_induction
#print axioms exhaustive_all_count_C_union
#print axioms sharp_surplus_boundary_read_guards
#print axioms whole_reference_binary_tail_polynomial_identity
#print axioms whole_even_fibonacci_Cassini
end AllBinaryTernaryCompleteC
