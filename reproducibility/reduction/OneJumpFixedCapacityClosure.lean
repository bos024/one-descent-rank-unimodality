import Mathlib

set_option maxHeartbeats 0
namespace OneJumpFixedCapacityClosure

def minor (d : ℕ → ℤ) (n : ℕ) : ℤ := d n^2-d (n-1)*d (n+1)

private theorem window_LC (A B C D : ℤ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 < B)
    (h1 : 0 ≤ B^2-A*C) (h2 : 0 ≤ C^2-B*D) :
    0 ≤ (B+C)^2-(A+B)*(C+D) := by
  have hp := mul_nonneg hC h1
  have hq := mul_nonneg hA h2
  have hc : 0 ≤ B*C-A*D := by
    have hh : 0 ≤ B*(B*C-A*D) := by nlinarith only [hp,hq]
    exact (mul_nonneg_iff_of_pos_left hB).mp hh
  nlinarith only [h1,h2,hc]

-- Generic whole-tail induction with arbitrary reference and a terminal trim.
theorem reference_trim_full_tail_induction
    (d : ℕ → ℕ → ℤ) (J : ℕ → ℕ) (r : ℕ → ℤ) (H : ℕ)
    (hH : 2 ≤ H)
    (hp : ∀ h n, H ≤ h → n ≤ J h → 1 ≤ d h n)
    (hz : ∀ h n, H ≤ h → J h < n → d h n=0)
    (hr : ∀ n, 0 ≤ r n)
    (hpre : ∀ h n, H ≤ h → n ≤ h → d h n=r n)
    (hdef : ∀ h, H ≤ h → d h (h+1) ≤ r (h+1)-1)
    (hboundary : ∀ h, H ≤ h → 0 ≤ r h^2-r (h-1)*(r (h+1)-1))
    (hJ : ∀ h, H ≤ h → J (h+1) ≤ J h+2)
    (heq : ∀ h n, H ≤ h → h+1 ≤ n → n ≤ J h+1 →
      d (h+1) n=d h (n-1)+d h (n-2))
    (hle : ∀ h n, H ≤ h → h+1 ≤ n →
      d (h+1) n ≤ d h (n-1)+d h (n-2))
    (hbase : ∀ n, H ≤ n → 0 ≤ minor (d H) n) :
    ∀ h, H ≤ h → ∀ n, h ≤ n → 0 ≤ minor (d h) n := by
  intro h hh
  induction h, hh using Nat.le_induction with
  | base => exact hbase
  | succ h hh ih =>
    intro n hn
    have hn3 : 3 ≤ n := by omega
    have hnon : ∀ i, 0 ≤ d h i := by
      intro i
      by_cases hi : i ≤ J h
      · have hv := hp h i hh hi;omega
      · rw [hz h i hh (by omega)]
    by_cases hout : J (h+1)<n
    · have h0 := hz (h+1) n (by omega) hout
      have h1 := hz (h+1) (n+1) (by omega) (by omega)
      simp [minor,h0,h1]
    by_cases hlast : n=J (h+1)
    · have h1 := hz (h+1) (n+1) (by omega) (by omega)
      simp only [minor,h1,mul_zero,sub_zero]
      positivity
    by_cases hb : n=h+1
    · subst n
      have hp0 := hpre (h+1) h (by omega) (by omega)
      have hp1 := hpre (h+1) (h+1) (by omega) (by omega)
      have hd := hdef (h+1) (by omega)
      have hn0 : h+1-1=h := by omega
      have hm := mul_le_mul_of_nonneg_left hd (hr h)
      have hbound := hboundary (h+1) (by omega)
      rw [hn0] at hbound
      dsimp [minor]
      rw [hp0,hp1]
      nlinarith only [hm,hbound]
    have hnJ : n ≤ J h+1 := by have hj := hJ h hh;omega
    have hi1 := ih (n-2) (by omega)
    have hi2 := ih (n-1) (by omega)
    have he1 : n-2-1=n-3 := by omega
    have he2 : n-2+1=n-1 := by omega
    have he3 : n-1-1=n-2 := by omega
    have he4 : n-1+1=n := by omega
    dsimp [minor] at hi1 hi2
    rw [he1,he2] at hi1
    rw [he3,he4] at hi2
    have hbp := hp h (n-2) hh (by omega)
    have hs := window_LC (d h (n-3)) (d h (n-2)) (d h (n-1)) (d h n)
      (hnon _) (hnon _) (by omega) hi1 hi2
    have ep := heq h (n-1) hh (by omega) (by omega)
    have ec := heq h n hh (by omega) hnJ
    have en := hle h (n+1) hh (by omega)
    have he5 : n-1-2=n-3 := by omega
    have he6 : n+1-1=n := by omega
    have he7 : n+1-2=n-1 := by omega
    rw [he3,he5] at ep
    rw [he6,he7] at en
    have hm := mul_le_mul_of_nonneg_left en
      (show 0 ≤ d h (n-2)+d h (n-3) by have hp0 := hnon (n-3);omega)
    dsimp [minor]
    rw [ep,ec]
    nlinarith only [hs,hm]

theorem reference_amplitude_start_budget (f fp fpp sign : ℤ)
    (hf : f=fp+fpp) (hpos : 1 ≤ fpp) (hs : -1 ≤ sign) :
    f+2*fp-1-sign ≤ 2*f+fp-1 := by omega

theorem reference_first_defect_seed_ratios (a b c d C delta : ℝ)
    (hc : c=a+b) (hd : d=b+c) (hC : 0 ≤ C) (ha : C ≤ a)
    (hab : a ≤ b) (hdelta : 1 ≤ delta)
    (hminus : -C ≤ b^2-a*c) (hplus : b^2-a*c ≤ C) :
    a*(d-delta) ≤ b*c ∧ b*(d-delta) ≤ c^2 := by
  have hda := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ delta-1 by linarith)
  have hdb := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ delta-1 by linarith)
  rw [hd,hc] at *
  constructor <;> nlinarith only [hda,hdb,hminus,hplus,ha,hab]

theorem two_integrations_prefix_ratio_propagation
    (D F G : ℕ → ℝ) (lam : ℝ) (h K : ℕ) (_hh : 1 ≤ h)
    (hF : ∀ k, h ≤ k → k ≤ K → F k=F (k-1)+D k)
    (hG : ∀ k, h ≤ k → k ≤ K → G k=G (k-1)+F k)
    (hD : ∀ k, h+1 ≤ k → k ≤ K → lam*D (k-1) ≤ D k)
    (hFs : lam*F (h-1) ≤ F h) (hGs : lam*G (h-1) ≤ G h) :
    ∀ k, h ≤ k → k ≤ K → lam*F (k-1) ≤ F k ∧ lam*G (k-1) ≤ G k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _;exact ⟨hFs,hGs⟩
  | succ k hk ih =>
    intro hkK
    have hi := ih (by omega)
    have hf0 := hF k hk (by omega)
    have hf1 := hF (k+1) (by omega) hkK
    have hg0 := hG k hk (by omega)
    have hg1 := hG (k+1) (by omega) hkK
    have hd := hD (k+1) (by omega) hkK
    have hidx : k+1-1=k := by omega
    rw [hidx] at hf1 hg1 hd
    have hmF := congrArg (fun x => lam*x) hf0
    have hmG := congrArg (fun x => lam*x) hg0
    have hnewF : lam*F k ≤ F (k+1) := by nlinarith only [hf1,hmF,hi.1,hd]
    have hnewG : lam*G k ≤ G (k+1) := by nlinarith only [hg1,hmG,hi.2,hnewF]
    simpa only [hidx] using And.intro hnewF hnewG

theorem fixed_capacity_padding_read_geometry (h L alpha : ℕ)
    (ha : h+L ≤ alpha) : 2*h+L+1 < h+alpha+2 := by omega

#print axioms reference_trim_full_tail_induction
#print axioms reference_amplitude_start_budget
#print axioms reference_first_defect_seed_ratios
#print axioms two_integrations_prefix_ratio_propagation
#print axioms fixed_capacity_padding_read_geometry
end OneJumpFixedCapacityClosure
