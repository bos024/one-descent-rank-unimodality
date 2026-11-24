import Mathlib

set_option maxHeartbeats 0
namespace ForwardPositiveDifferenceCenters

theorem positive_subtraction_reflection (aL aR bL bR : ℝ)
    (ha : aR ≤ aL) (hb : bL ≤ bR) :
    max (aR-bR) 0 ≤ max (aL-bL) 0 := by
  apply max_le_max
  · linarith
  · exact le_rfl

theorem source_append_identity (z S U F D C Fn Dn Cn : ℝ)
    (hS : S=z+z^2*U) (hF : (1-z)*F=1+z^2*D-C)
    (hn : Fn=1+S*F) (hD : Dn=U+S*D) (hC : Cn=S*C) :
    (1-z)*Fn=1+z^2*Dn-Cn := by
  rw [hn,hD,hC]
  calc
    (1-z)*(1+S*F)=1-z+S*((1-z)*F) := by ring
    _=1+z^2*(U+S*D)-S*C := by rw [hF,hS];ring

theorem component_center_bound (W h prefMass i : ℤ)
    (hp : 0 ≤ prefMass) (hi : 1 ≤ i) :
    W-prefMass+h-i-2 ≤ W+h-3 := by omega

theorem correction_center_difference (alpha W h : ℤ) :
    (2*(alpha+h-1)+(W-h))-(W+h-3)=2*alpha+1 := by ring

theorem reflected_first_maximum (f : ℕ → ℝ) (K j : ℕ)
    (hj : j ≤ K) (hreflect : f j ≤ f (K-j))
    (hfirst : ∀ i < j, f i < f j) : 2*j ≤ K := by
  by_contra hn
  have hi : K-j < j := by omega
  have hh := hfirst (K-j) hi
  linarith

theorem layer_endpoint_bound (L R K : ℕ)
    (hR : R ≤ K) (hL : L ≤ K-R) : L+R ≤ K := by omega

theorem shifted_first_mode_bound (j W h : ℕ)
    (hWh : 3 ≤ W+h) (hj : 2*j ≤ W+h-3) :
    j+2 ≤ (W+h+1)/2 := by omega

theorem odd_uniform_first_increment (m : ℤ) :
    (3*m-2*(m-1)-m)-1=1 := by ring

theorem odd_uniform_next_increment (m : ℤ) :
    (3*m+1-2*m-(m+1))-1=-1 := by ring

theorem odd_uniform_mode_sharp (m : ℕ) :
    (3*(2*m+1)+4)/2=3*m+3 := by omega

theorem four_cover_no_double_exclusions (a b c d n s : ℤ)
    (_hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hn : n=d+s) (hs : 5 ≤ s) (hmode : 2*n ≤ a+b+c+4) :
    6 ≤ a ∧ n < a+b := by omega

theorem finite_ones_critical_geometry (a b c d n s alpha : ℤ)
    (_hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hn : n=d+s) (hs : 5 ≤ s) (halpha : 1 ≤ alpha)
    (hW : 0 ≤ a+b+c-2*n+4-max (n-alpha-3) 0+
      max (n-alpha-3-a) 0+max (n-alpha-3-b) 0+max (n-alpha-3-c) 0) :
    n-alpha-3 < a ∧ max (n-alpha-3) 0 ≤ a+b+c-2*n+4 := by omega

theorem critical_parameter_identity (a b c d n s u v w Z : ℤ)
    (hb : b=a+v) (hc : c=b+w) (hd : d=c+u)
    (hn : n=d+s) (hZ : Z=a+b+c-2*n+4) :
    a=2*s+w+2*u-4+Z := by omega

theorem finite_negative_y_cone (x r s : ℤ)
    (hx : 1 ≤ x) (hy : x+3-r < 0) (hrs : r ≤ s) :
    0 ≤ x-1 ∧ 0 ≤ r-x-4 ∧ 0 ≤ s-r ∧ 5 ≤ r := by omega

#print axioms positive_subtraction_reflection
#print axioms source_append_identity
#print axioms component_center_bound
#print axioms correction_center_difference
#print axioms reflected_first_maximum
#print axioms layer_endpoint_bound
#print axioms shifted_first_mode_bound
#print axioms odd_uniform_first_increment
#print axioms odd_uniform_next_increment
#print axioms odd_uniform_mode_sharp
#print axioms four_cover_no_double_exclusions
#print axioms finite_ones_critical_geometry
#print axioms critical_parameter_identity
#print axioms finite_negative_y_cone
end ForwardPositiveDifferenceCenters
