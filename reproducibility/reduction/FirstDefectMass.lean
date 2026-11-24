import Mathlib

set_option maxHeartbeats 0
namespace FirstDefectMass

def flag (t : ℕ → ℤ) (i : ℕ) : ℤ := if t i=(i:ℤ)+1 then 1 else 0
def surplus (t : ℕ → ℤ) (i : ℕ) : ℤ := max (t i-(i:ℤ)-2) 0

theorem twice_staircase (n : ℕ) :
    2*(∑ i ∈ Finset.range n,((i:ℤ)+1))=(n:ℤ)*((n:ℤ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem point_decomposition (t : ℕ → ℤ) (i : ℕ) (ht : (i:ℤ)+1 ≤ t i) :
    t i=(i:ℤ)+2-flag t i+surplus t i := by
  unfold flag surplus
  split_ifs <;> omega

theorem sharp_mass_identity (n : ℕ) (t : ℕ → ℤ) (extra eps a d : ℤ)
    (ht : ∀ i<n,(i:ℤ)+1 ≤ t i)
    (ha : a=extra+∑ i ∈ Finset.range n,t i)
    (hd : d=eps+∑ i ∈ Finset.range n,flag t i) :
    2*a=(n:ℤ)*((n:ℤ)+1)+
      2*((n:ℤ)+1-d+(extra+eps-1)+∑ i ∈ Finset.range n,surplus t i) := by
  have hs : (∑ i ∈ Finset.range n,t i)=
      (∑ i ∈ Finset.range n,((i:ℤ)+1))+(n:ℤ)-
      (∑ i ∈ Finset.range n,flag t i)+(∑ i ∈ Finset.range n,surplus t i) := by
    calc
      (∑ i ∈ Finset.range n,t i)=
          ∑ i ∈ Finset.range n,((i:ℤ)+2-flag t i+surplus t i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact point_decomposition t i (ht i (Finset.mem_range.mp hi))
      _ = _ := by
        simp [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        ring
  have hh := twice_staircase n
  rw [ha,hd,hs]
  nlinarith

theorem sharp_mass_bound (n : ℕ) (t : ℕ → ℤ) (extra eps a d : ℤ)
    (ht : ∀ i<n,(i:ℤ)+1 ≤ t i)
    (ha : a=extra+∑ i ∈ Finset.range n,t i)
    (hd : d=eps+∑ i ∈ Finset.range n,flag t i)
    (he : 1 ≤ extra+eps) :
    (n:ℤ)*((n:ℤ)+1)+2*((n:ℤ)+1-d) ≤ 2*a := by
  have hi := sharp_mass_identity n t extra eps a d ht ha hd
  have hs : 0 ≤ ∑ i ∈ Finset.range n,surplus t i :=
    Finset.sum_nonneg (fun i _ => le_max_right _ _)
  omega

theorem equality_classification (n : ℕ) (t : ℕ → ℤ) (extra eps a d : ℤ)
    (ht : ∀ i<n,(i:ℤ)+1 ≤ t i)
    (ha : a=extra+∑ i ∈ Finset.range n,t i)
    (hd : d=eps+∑ i ∈ Finset.range n,flag t i)
    (he : 1 ≤ extra+eps) :
    (2*a=(n:ℤ)*((n:ℤ)+1)+2*((n:ℤ)+1-d)) ↔
      (extra+eps=1 ∧ ∀ i<n,t i ≤ (i:ℤ)+2) := by
  have hi := sharp_mass_identity n t extra eps a d ht ha hd
  have hs : 0 ≤ ∑ i ∈ Finset.range n,surplus t i :=
    Finset.sum_nonneg (fun i _ => le_max_right _ _)
  constructor
  · intro hh
    have hz : (∑ i ∈ Finset.range n,surplus t i)=0 := by omega
    constructor
    · omega
    · intro i hni
      have hp := Finset.single_le_sum (s:=Finset.range n) (f:=surplus t)
        (fun j _ => le_max_right _ _) (Finset.mem_range.mpr hni)
      rw [hz] at hp
      unfold surplus at hp
      omega
  · rintro ⟨hee,hh⟩
    have hz : (∑ i ∈ Finset.range n,surplus t i)=0 := by
      apply Finset.sum_eq_zero
      intro i hni
      have hbound := hh i (Finset.mem_range.mp hni)
      unfold surplus
      omega
    omega

theorem defect_upper_bound (n : ℕ) (t : ℕ → ℤ) (eps d : ℤ)
    (he : eps ≤ 1) (hd : d=eps+∑ i ∈ Finset.range n,flag t i) :
    d ≤ (n:ℤ)+1 := by
  have hs : (∑ i ∈ Finset.range n,flag t i) ≤ (n:ℤ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,(1:ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        unfold flag
        split_ifs <;> omega
      _ = _ := by simp
  omega

#print axioms sharp_mass_identity
#print axioms sharp_mass_bound
#print axioms equality_classification
#print axioms defect_upper_bound
end FirstDefectMass
