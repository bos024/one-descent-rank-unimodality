import Mathlib
set_option maxHeartbeats 2000000
namespace StationaryTernaryReferenceBase
theorem exact_q_interval (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    618033988749/1000000000000 ≤ q ∧ q ≤ 618033988750/1000000000000 := by
  constructor
  · by_contra! h
    have hs := mul_self_le_mul_self hp (le_of_lt h)
    nlinarith
  · by_contra! h
    have hs := mul_self_le_mul_self (show (0:ℝ) ≤ 618033988750/1000000000000 by norm_num) (le_of_lt h)
    nlinarith
theorem complete_fixed_six_residual_tail (q : ℝ) (hq : q^2+q=1) (hp : 0 ≤ q) :
    0<((37:ℝ)+(-44:ℝ)*q) ∧
    0<((67:ℝ)+(-81:ℝ)*q) ∧
    0<((118:ℝ)+(-148:ℝ)*q) ∧
    0<((200:ℝ)+(-266:ℝ)*q) ∧
    0<((328:ℝ)+(-466:ℝ)*q) ∧
    0<((527:ℝ)+(-794:ℝ)*q) ∧
    0<((843:ℝ)+(-1321:ℝ)*q) ∧
    0<((1352:ℝ)+(-2164:ℝ)*q) ∧
    0<((2179:ℝ)+(-3516:ℝ)*q) ∧
    0<((3521:ℝ)+(-5695:ℝ)*q) ∧
    0<((5696:ℝ)+(-9216:ℝ)*q) ∧
    0<((172:ℝ)+(-235:ℝ)*q) ∧
    0<((882:ℝ)+(-1264:ℝ)*q) ∧
    0<((3084:ℝ)+(-4656:ℝ)*q) ∧
    0<((8136:ℝ)+(-12666:ℝ)*q) ∧
    0<((16075:ℝ)+(-25600:ℝ)*q) ∧
    0<((24970:ℝ)+(-40115:ℝ)*q) ∧
    0<((29267:ℝ)+(-47269:ℝ)*q) ∧
    0<((25925:ℝ)+(-41920:ℝ)*q) ∧
    0<((15426:ℝ)+(-24959:ℝ)*q) := by
  have hi := exact_q_interval q hq hp
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩ <;> nlinarith [hq,hi.1,hi.2]
#print axioms complete_fixed_six_residual_tail
end StationaryTernaryReferenceBase
