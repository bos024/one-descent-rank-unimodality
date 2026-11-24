import Mathlib

set_option maxHeartbeats 0
namespace MainBoxDerivativeEnvelope

def uniform (q : ℤ → ℤ) (t : ℕ) (n : ℤ) : ℤ :=
  ∑ i ∈ Finset.range t, q (n-(i:ℤ))

def step (q : ℤ → ℤ) (t : ℕ) (a n : ℤ) : ℤ :=
  uniform q t n+(if n=a then 1 else 0)

theorem uniform_difference_bound (q K : ℤ → ℤ) (t : ℕ)
    (h : ∀ n,q n-q (n-1) ≤ K n) (n : ℤ) :
    uniform q t n-uniform q t (n-1) ≤ uniform K t n := by
  unfold uniform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh:=h (n-(i:ℤ))
  have ha : n-1-(i:ℤ)=(n-(i:ℤ))-1 := by ring
  rw [ha]
  exact hh

theorem terminal_unit_preserves_bound (q K : ℤ → ℤ) (t : ℕ) (a : ℤ)
    (h : ∀ n,q n-q (n-1) ≤ K n)
    (hK : ∀ n,0 ≤ K n)
    (ha : uniform q t a=0) (hap : uniform q t (a-1)=1) :
    ∀ n,step q t a n-step q t a (n-1) ≤ uniform K t n := by
  intro n
  have hb:=uniform_difference_bound q K t h n
  by_cases hn : n=a
  · subst n
    have hkn : 0 ≤ uniform K t a := Finset.sum_nonneg (fun i hi => hK _)
    unfold step
    have hne : a-1≠a := by omega
    simp [ha,hap,hne]
    exact hkn
  · unfold step
    split_ifs <;> omega

theorem rising_curvature_has_previous_growth (q0 q1 q2 : ℤ)
    (hq : 0<q1) (hinc : q0 ≤ q1 ∧ q1 ≤ q2)
    (hlc : q0*q2 ≤ q1*q1) (hd : 0<q2-2*q1+q0) :
    1 ≤ q1-q0 := by
  by_contra h
  have he : q0=q1 := by omega
  subst q0
  have hp : 0<q1*(q2-q1) := mul_pos hq (by omega)
  nlinarith

theorem curvature_resource (q0 q1 q2 K : ℤ)
    (hg : 1 ≤ q1-q0) (hD : q2-q1 ≤ K) :
    q2-2*q1+q0+1 ≤ K := by omega

theorem subcritical_all_rank_domain (k c g s b h m j : ℤ)
    (hk : 9 ≤ k) (hmass : k*(k-1) ≤ 2*c)
    (hg : 0 ≤ g ∧ g ≤ k-2) (hs : s ≤ g)
    (hb : b=c+s) (hh : 2*h ≤ b-1) (hm : m=b-h)
    (hj : 2*j ≤ g+s+1) :
    k+2*j-2 ≤ m := by
  have hp : 0 ≤ (k-2)*(k-9) := mul_nonneg (by omega) (by omega)
  have hc : 5*k-9 ≤ c := by nlinarith
  omega

#print axioms uniform_difference_bound
#print axioms terminal_unit_preserves_bound
#print axioms rising_curvature_has_previous_growth
#print axioms curvature_resource
#print axioms subcritical_all_rank_domain
end MainBoxDerivativeEnvelope
