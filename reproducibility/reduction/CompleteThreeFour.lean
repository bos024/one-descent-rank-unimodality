import Mathlib
set_option maxHeartbeats 4000000
namespace CompleteThreeFour

theorem true_cumulative_source_startups_from_ten (w r : ℝ)
    (hw : 10 ≤ w) (hr : 0≤r) (hrw : r≤w) :
    let m1 := w+1
    let m2 := (w+1)*(w+2)/2
    let m3 := (w+1)*(w+2)*(w+3)/6-r
    4 ≤ m1 ∧ 4*m1 ≤ m2 ∧ 4*m2 ≤ m3 ∧ m2 ≤ m1^2 ∧ m1*m3 ≤ m2^2 := by
  dsimp
  have w0 : 0≤w := by linarith
  have p0 := mul_nonneg (show 0≤w+1 by linarith) (show 0≤w-6 by linarith)
  have p1 : 0≤(w+1)*(w+2)*(w+3)/6-w-4*((w+1)*(w+2)/2) := by
    let x := w-10
    have hx : 0≤x := by dsimp [x]; linarith
    have he : w=10+x := by dsimp [x]; ring
    rw [he]; ring_nf; positivity
  have p2 : 0≤((w+1)*(w+2)/2)^2-(w+1)*((w+1)*(w+2)*(w+3)/6) := by
    have hid : ((w+1)*(w+2)/2)^2-(w+1)*((w+1)*(w+2)*(w+3)/6)=
      w*(w+1)^2*(w+2)/12 := by ring
    rw [hid]; positivity
  have p3 := mul_nonneg (show 0≤w+1 by linarith) hr
  refine ⟨by linarith,by nlinarith only [p0],by linarith,?_,?_⟩
  · nlinarith only [w0,sq_nonneg w]
  · nlinarith only [p2,p3]

theorem complete_finite_parameter_and_padding_reduction (r s alpha n : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    let L := (4*r+5*s)/2
    let w := r+s
    (w ≤ L ∧ (L-w+1 ≤ alpha → n ≤ L → n < alpha+w+1)) ∧
    (r < 50 → 8 ≤ max 8 ((r+4)/3) ∧ max 8 ((r+4)/3) ≤ 17) ∧
    (32<3*r+4*s → 3*s<r+2 → 10≤r+s ∧ 4*s+1≤r+s+2) ∧
    (7≤alpha → n≤7 → n<alpha+r+1) ∧
    (6≤r → n≤7 → n<r+2) := by
  dsimp
  omega

theorem whole_two_count_from_complete_finite_boundaries
    (P O : ℕ → ℕ → Prop) (star : ℕ → ℕ)
    (hlarge : ∀ r s,50≤r → P r s)
    (hpurefour : ∀ s,P 0 s) (hpurethree : ∀ r,P r 0)
    (hbase : ∀ r,0<r → r<50 → O r (star r))
    (hstep : ∀ r s,0<r → r<50 → star r ≤ s → O r s → O r (s+1))
    (hC : ∀ r s,0<r → r<50 → O r s → P r s)
    (hfinite : ∀ r s,0<r → r<50 → 0 < s → s < star r → P r s) :
    ∀ r s,P r s := by
  intro r s
  by_cases hr : 50≤r
  · exact hlarge r s hr
  · by_cases hr0 : r=0
    · subst r; exact hpurefour s
    · by_cases hs0 : s=0
      · subst s; exact hpurethree r
      · by_cases hs : s < star r
        · exact hfinite r s (by omega) (by omega) (by omega) hs
        · have hge : star r ≤ s := by omega
          obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hge
          have hall : ∀ j : ℕ,O r (star r+j) := by
            intro j
            induction j with
            | zero => simpa using hbase r (by omega) (by omega)
            | succ j ih =>
              have hh := hstep r (star r+j) (by omega) (by omega) (by omega) ih
              simpa [Nat.add_assoc] using hh
          rw [hk]
          exact hC r _ (by omega) (by omega) (hall k)

#print axioms true_cumulative_source_startups_from_ten
#print axioms complete_finite_parameter_and_padding_reduction
#print axioms whole_two_count_from_complete_finite_boundaries
end CompleteThreeFour
