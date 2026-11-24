import Mathlib
namespace FirstMissingTwelveHeadGuards

def mainDegree (K : ℕ) : ℕ := 1+(K-2)*(K-1)/2
def otherDegree (K : ℕ) : ℕ := 1+(K-3)*(K-2)/2
def headBound (K : ℕ) : ℕ := mainDegree K/2

theorem all_next_three_genuine_strict_head_budgets (K : ℕ)
    (hK0 : 10 ≤ K) (hK1 : K ≤ 12) :
    2*headBound K ≤ mainDegree K ∧ headBound K ≤ otherDegree K ∧
    K-4 ≤ headBound K := by
  interval_cases K <;> norm_num [mainDegree,otherDegree,headBound]

theorem canonical_owner_count_and_padding_reduction (K alpha d h D : ℕ)
    (halpha : 1 ≤ alpha) (hd : alpha+d=K) (hd6 : 6 ≤ d) (hhD : h ≤ D)
    (hfour : 4 ≤ h → 7 ≤ d) (hsix : 6 ≤ h → 9 ≤ d) :
    alpha ≤ K-6 ∧
    h ≤ min D (if d ≤ 6 then 3 else if d ≤ 8 then 5 else D) := by
  constructor
  · omega
  · apply le_min hhD
    split_ifs <;> omega

theorem whole_proper_head_read_and_raw_owner_safety (a b j n k S : ℕ)
    (hj : j+n=a+b) (hsecond : k+n+2<a+b)
    (howner : j ≤ a+1) (hhead : j-2 ≤ S) :
    k+1 ≤ S ∧ k+1 ≤ a-1 := by omega

theorem every_negative_birth_exception_has_a_genuine_strict_head
    (K a b j n k : ℕ) (hK0 : 10 ≤ K) (hK1 : K ≤ 12)
    (hmiss : a+2<K) (hj : j=a+1) (hjn : j+n=a+b)
    (hsecond : k+n+2<a+b) :
    k+1 ≤ headBound K ∧ k+1 ≤ a-1 := by
  have hbudget := (all_next_three_genuine_strict_head_budgets K hK0 hK1).2.2
  apply whole_proper_head_read_and_raw_owner_safety a b j n k (headBound K)
    hjn hsecond (by omega)
  omega

#print axioms all_next_three_genuine_strict_head_budgets
#print axioms canonical_owner_count_and_padding_reduction
#print axioms whole_proper_head_read_and_raw_owner_safety
#print axioms every_negative_birth_exception_has_a_genuine_strict_head
end FirstMissingTwelveHeadGuards
