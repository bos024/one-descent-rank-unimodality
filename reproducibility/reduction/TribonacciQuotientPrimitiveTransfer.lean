import Mathlib
set_option maxHeartbeats 1000000
namespace TribonacciQuotientPrimitiveTransfer

theorem exact_binary_quotient_correction {R : Type*} [CommRing R]
    (z a b l J x y : R) (h : l*b=1) :
    (1+z)*((1+a*z+b*z^2)*J+x+y*z)
      =(1+a*z+b*z^2)*((1+z)*J+l*y)
        +(x-l*y)+(x+(1-l*a)*y)*z := by
  linear_combination -(y*z^2)*h

theorem exact_ternary_quotient_correction {R : Type*} [CommRing R]
    (z a b l J x y : R) (h : l*b=1) :
    (1+z+z^2)*((1+a*z+b*z^2)*J+x+y*z)
      =(1+a*z+b*z^2)*((1+z+z^2)*J+l*(x+y-a*l*y)+l*y*z)
        +(x-l*(x+y-a*l*y))
        +(x+y-a*l*(x+y-a*l*y)-l*y)*z := by
  linear_combination -((x+y-a*l*y)*z^2+y*z^3)*h

theorem whole_primitive_three_head_to_tail_join (D C : ℕ → ℝ)
    (hagree : ∀ n,3 ≤ n → D n=C n)
    (hhead : ∀ n,1 ≤ n → n ≤ 3 → D (n-1)*D (n+1) ≤ D n^2)
    (hC : ∀ n,1 ≤ n → C (n-1)*C (n+1) ≤ C n^2) :
    ∀ n,1 ≤ n → D (n-1)*D (n+1) ≤ D n^2 := by
  intro n hn
  by_cases hh : n ≤ 3
  · exact hhead n hn hh
  · rw [hagree (n-1) (by omega),hagree n (by omega),hagree (n+1) (by omega)]
    exact hC n hn

#print axioms exact_binary_quotient_correction
#print axioms exact_ternary_quotient_correction
#print axioms whole_primitive_three_head_to_tail_join

end TribonacciQuotientPrimitiveTransfer
