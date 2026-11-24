import Mathlib

set_option maxHeartbeats 0

namespace LowerFrechetLC

theorem decreasing_lower_frechet_payment (M A x C B y D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hG : 0 ≤ A+B-M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hAx : x ≤ A) (hBy : y ≤ B)
    (hMx : x ≤ M) (hMy : y ≤ M)
    (hLCa : 0 ≤ x^2-A*C) (hLCb : 0 ≤ y^2-B*D) :
    0 ≤ (x+y-M)^2-(A+B-M)*(C+D-M) := by
  have hd : 0 ≤ A-x := by linarith only [hAx]
  have he : 0 ≤ B-y := by linarith only [hBy]
  have hmx : 0 ≤ M-x := by linarith only [hMx]
  have hmy : 0 ≤ M-y := by linarith only [hMy]
  have h1 := mul_nonneg (mul_nonneg (le_of_lt hB) hG) hLCa
  have h2 := mul_nonneg (mul_nonneg (le_of_lt hA) hG) hLCb
  have h3 := mul_nonneg (mul_nonneg (le_of_lt hB) hd)
    (add_nonneg (mul_nonneg hmy hd) (mul_nonneg hx he))
  have h4 := mul_nonneg (mul_nonneg (le_of_lt hA) he)
    (add_nonneg (mul_nonneg hmx he) (mul_nonneg hy hd))
  have hid : A*B*((x+y-M)^2-(A+B-M)*(C+D-M))
      = B*(A+B-M)*(x^2-A*C)+A*(A+B-M)*(y^2-B*D)
        +B*(A-x)*((M-y)*(A-x)+x*(B-y))
        +A*(B-y)*((M-x)*(B-y)+y*(A-x)) := by ring
  have hpay : 0 ≤ A*B*((x+y-M)^2-(A+B-M)*(C+D-M)) := by
    rw [hid]
    exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  by_contra hbad
  have hneg:=mul_neg_of_pos_of_neg (mul_pos hA hB)
    (show (x+y-M)^2-(A+B-M)*(C+D-M)<0 by linarith only [hbad])
  linarith only [hpay,hneg]

theorem entire_lower_frechet_LC_clipping (M : ℝ) (a b : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (haM : ∀ n, a n ≤ M) (hbM : ∀ n, b n ≤ M)
    (haD : ∀ n, a (n+1) ≤ a n) (hbD : ∀ n, b (n+1) ≤ b n)
    (haLC : ∀ n, 0 ≤ a (n+1)^2-a n*a (n+2))
    (hbLC : ∀ n, 0 ≤ b (n+1)^2-b n*b (n+2)) :
    ∀ n, 0 ≤ (max (a (n+1)+b (n+1)-M) 0)^2
      -max (a n+b n-M) 0*max (a (n+2)+b (n+2)-M) 0 := by
  intro n
  by_cases hc : a (n+1)+b (n+1)-M ≤ 0
  · have hn : a (n+2)+b (n+2)-M ≤ 0 := by
      have h1:=haD (n+1)
      have h2:=hbD (n+1)
      norm_num only [Nat.add_assoc,Nat.reduceAdd] at h1 h2
      linarith only [hc,h1,h2]
    rw [max_eq_right hc,max_eq_right hn]
    simp
  · have hcpos : 0 < a (n+1)+b (n+1)-M := by linarith only [hc]
    have hp : 0 < a n+b n-M := by
      have h1:=haD n
      have h2:=hbD n
      linarith only [hcpos,h1,h2]
    by_cases hn : a (n+2)+b (n+2)-M ≤ 0
    · rw [max_eq_right hn]
      simp only [mul_zero,sub_zero]
      exact sq_nonneg _
    · rw [max_eq_left (le_of_lt hcpos),max_eq_left (le_of_lt hp),
          max_eq_left (show 0 ≤ a (n+2)+b (n+2)-M by linarith only [hn])]
      apply decreasing_lower_frechet_payment M (a n) (a (n+1)) (a (n+2))
        (b n) (b (n+1)) (b (n+2))
      · have h1:=haD n
        have h2:=hbM (n+1)
        linarith only [hcpos,h1,h2]
      · have h1:=hbD n
        have h2:=haM (n+1)
        linarith only [hcpos,h1,h2]
      · exact le_of_lt hp
      · exact ha0 _
      · exact hb0 _
      · exact haD _
      · exact hbD _
      · exact haM _
      · exact hbM _
      · exact haLC _
      · exact hbLC _

#print axioms decreasing_lower_frechet_payment
#print axioms entire_lower_frechet_LC_clipping

end LowerFrechetLC
