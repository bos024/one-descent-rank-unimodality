import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace TripleSubdegreeCEntrance

theorem all_padding_three_loss_payments (w r : ℝ) (hw : 6 ≤ w) (hr : 1 ≤ r) :
    3*(2*w+1) ≤ w^2+2*r+2 ∧
    3*(w+2) ≤ (w^2-w+2*r)/2+2*w+2 ∧
    3*(w+1) ≤ (w^2-w+2*r)/2+w+3 ∧
    3*(w+1) ≤ (w^2-w+2*r)/2+w+2 := by
  constructor
  · nlinarith only [sq_nonneg (w-6),hw,hr]
  constructor
  · nlinarith only [sq_nonneg (w-6),hw,hr]
  constructor <;> nlinarith only [sq_nonneg (w-6),hw,hr]

theorem first_ordinary_seed_identity (x y a b c : ℝ) :
    (y-a)*(x-b)-(x-1)*(y-c)=x*(c-a)-y*(b-1)+a*b-c := by ring

theorem second_ordinary_seed_identity (x y a b c : ℝ) :
    (x+y-a-b)*(x-b)-(y-a)*(y-c)=
      x^2+x*y-y^2-x*(a+2*b)+y*(a-b+c)+b^2+a*b-a*c := by ring

theorem first_ordinary_seed_paid (x y a b c : ℝ)
    (hx : 2 ≤ x) (hy : y ≤ 2*x) (ha : 1 ≤ a) (_haa : a ≤ 2)
    (hb : 2*a ≤ b) (hc : 3*b ≤ c) :
    2 ≤ x*(c-a)-y*(b-1)+a*b-c := by
  have hb2 : 2 ≤ b := by linarith only [ha,hb]
  have ht : 0 ≤ c-a-2*b+2 := by linarith only [hc,hb,ha]
  have h1 := mul_nonneg (show 0 ≤ 2*x-y by linarith only [hy])
    (show 0 ≤ b-1 by linarith only [hb2])
  have h2 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx]) ht
  have h3 := mul_nonneg (show 0 ≤ a-1 by linarith only [ha])
    (show 0 ≤ b-2 by linarith only [hb2])
  nlinarith only [h1,h2,h3,hc]

theorem second_ordinary_seed_paid (x y a b c A : ℝ)
    (hx : 2 ≤ x) (hy : x ≤ y) (ha : 1 ≤ a) (haa : a ≤ 2)
    (hb : 2*a ≤ b) (hc : 3*b ≤ c) (hA : 0 < A) :
    0 < A-x*(a+2*b)+y*(a-b+c)+b^2+a*b-a*c := by
  have hp : 0 ≤ a-b+c := by linarith only [ha,hb,hc]
  have h1 := mul_nonneg (show 0 ≤ y-x by linarith only [hy]) hp
  have h2 := mul_nonneg (show 0 ≤ x-a by linarith only [hx,haa])
    (show 0 ≤ c-3*b by linarith only [hc])
  have h3 := mul_nonneg (show 0 ≤ b by linarith only [ha,hb])
    (show 0 ≤ b-2*a by linarith only [hb])
  nlinarith only [h1,h2,h3,hA]

theorem strict_subgolden_actual_entrance (x y b c p : ℝ)
    (hgap : 0 < p*x-y) (hp : p ≤ 2) (hb : 0 < b) (hc : 3*b ≤ c) :
    0 < p*(x-b)-(y-c) := by
  have h1 := mul_nonneg (show 0 ≤ 2-p by linarith only [hp]) (le_of_lt hb)
  nlinarith only [h1,hgap,hc,hb]

#print axioms all_padding_three_loss_payments
#print axioms first_ordinary_seed_identity
#print axioms second_ordinary_seed_identity
#print axioms first_ordinary_seed_paid
#print axioms second_ordinary_seed_paid
#print axioms strict_subgolden_actual_entrance

end TripleSubdegreeCEntrance
