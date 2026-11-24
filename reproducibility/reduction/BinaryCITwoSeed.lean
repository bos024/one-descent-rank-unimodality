import Mathlib

namespace BinaryCITwoSeed

theorem first_Cassini_seed_strict (A b c d delta : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hd : 1 ≤ delta)
    (hCassini : c^2-b*d=A) : 0 < c^2-b*(d-delta) := by
  have hprod := mul_pos hb (show 0 < delta by linarith only [hd])
  nlinarith only [hA,hCassini,hprod]

theorem second_Cassini_seed_full_parameter_bound
    (A b c d e delta eta W : ℝ)
    (hA : 0 < A) (hc : A ≤ c) (hbc : b ≤ c) (hrec : d=b+c)
    (hd : 1 ≤ delta) (hW : 3 ≤ W) (heta : delta*(W+1)+1 ≤ eta)
    (hCassini : d^2-c*e=-A) :
    delta^2 ≤ (d-delta)^2-c*(e-eta) := by
  have hc0 : 0 ≤ c := by linarith only [hA,hc]
  have hd0 : 0 ≤ delta := by linarith only [hd]
  have hdle : d ≤ 2*c := by linarith only [hrec,hbc]
  have he := mul_nonneg hc0
    (show 0 ≤ eta-(delta*(W+1)+1) by linarith only [heta])
  have hx := mul_nonneg hd0
    (show 0 ≤ 2*c-d by linarith only [hdle])
  have hz := mul_nonneg (mul_nonneg hd0
    (show 0 ≤ W-3 by linarith only [hW])) hc0
  nlinarith only [he,hx,hz,hc,hCassini]

theorem positive_part_preserves_strict_seed (c middle next : ℝ)
    (hm : 0 < middle) (hraw : 0 < middle^2-c*next) :
    0 < (max middle 0)^2-c*(max next 0) := by
  rw [max_eq_left (le_of_lt hm)]
  by_cases hn : 0 ≤ next
  · rw [max_eq_left hn]
    exact hraw
  · rw [max_eq_right (by linarith only [hn])]
    simpa using sq_pos_of_pos hm

#print axioms first_Cassini_seed_strict
#print axioms second_Cassini_seed_full_parameter_bound
#print axioms positive_part_preserves_strict_seed

end BinaryCITwoSeed
