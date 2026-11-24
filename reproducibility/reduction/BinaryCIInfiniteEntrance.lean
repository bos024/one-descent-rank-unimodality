import Mathlib

set_option maxHeartbeats 0

namespace BinaryCIInfiniteEntrance

theorem backward_geometric_LC_transport (p xp x y z : ℝ)
    (hp : 0 < p) (hx : 0 ≤ x)
    (hb : 0 ≤ p*xp-x) (hbn : 0 < p*x-y)
    (hnext : 0 ≤ y^2-x*z)
    (hdeficit : 0 ≤ (p*x-y)^2-(p*xp-x)*(p*y-z)) :
    0 ≤ x^2-xp*y := by
  have heq : x*((p*x-y)^2-(p*xp-x)*(p*y-z))
      +(p*xp-x)*(y^2-x*z)=p*(p*x-y)*(x^2-xp*y) := by ring
  have hleft := add_nonneg (mul_nonneg hx hdeficit) (mul_nonneg hb hnext)
  rw [heq] at hleft
  by_contra hbad
  have hneg := mul_neg_of_pos_of_neg (mul_pos hp hbn)
    (show x^2-xp*y < 0 by linarith only [hbad])
  linarith only [hleft,hneg]

theorem entire_finite_backward_integration (N : ℕ) (M : ℕ → ℝ)
    (htop : 0 ≤ M N)
    (hstep : ∀ k < N, 0 ≤ M (k+1) → 0 ≤ M k) :
    ∀ k ≤ N, 0 ≤ M k := by
  induction N with
  | zero =>
    intro k hk
    have h : k=0 := by omega
    simpa [h] using htop
  | succ N ih =>
    have hlast : 0 ≤ M N := hstep N (by omega) htop
    have hold := ih hlast (fun k hk => hstep k (by omega))
    intro k hk
    by_cases he : k=N+1
    · simpa [he] using htop
    · exact hold k (by omega)

theorem entire_geometric_deficit_LC_bridge (N : ℕ) (p : ℝ) (C : ℕ → ℝ)
    (hp : 0 < p)
    (hx : ∀ k ≤ N, 0 ≤ C (k+1))
    (hb : ∀ k ≤ N, 0 ≤ p*C k-C (k+1))
    (hbn : ∀ k < N, 0 < p*C (k+1)-C (k+2))
    (hdef : ∀ k < N,
      0 ≤ (p*C (k+1)-C (k+2))^2
        -(p*C k-C (k+1))*(p*C (k+2)-C (k+3)))
    (htop : 0 ≤ C (N+1)^2-C N*C (N+2)) :
    ∀ k ≤ N, 0 ≤ C (k+1)^2-C k*C (k+2) := by
  apply entire_finite_backward_integration N
    (fun k => C (k+1)^2-C k*C (k+2)) htop
  intro k hk hnext
  apply backward_geometric_LC_transport p (C k) (C (k+1)) (C (k+2)) (C (k+3))
    hp (hx k (by omega)) (hb k (by omega)) (hbn k hk)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using hnext
  · exact hdef k hk

theorem alternating_deficit_robust_budget (q bp b bn t P : ℝ)
    (hT : 0 ≤ bn+2*q*b+q^2*bp)
    (ht : -P ≤ t)
    (hbase : P*(bn+2*q*b+q^2*bp) ≤ b^2-bp*bn) :
    0 ≤ (b+q*t)^2-(bp-t)*(bn-q^2*t) := by
  have hpay := mul_nonneg (show 0 ≤ t+P by linarith only [ht]) hT
  have heq : (b+q*t)^2-(bp-t)*(bn-q^2*t)
      =(b^2-bp*bn)+t*(bn+2*q*b+q^2*bp) := by ring
  rw [heq]
  nlinarith only [hpay,hbase]

theorem first_robust_numerator_seed (q u a L2 : ℝ)
    (hq : q^2+q=1) (hqlo : 3/5 ≤ q) (hqhi : q ≤ 2/3)
    (hu : 3 ≤ u) (ha : 0 ≤ a) (hahi : 2*a ≤ u-1)
    (hL2 : L2 ≤ a^2) :
    let b := u+a-q
    let bn := u*(u-1)/2+u*a+L2-q*(u+a)+q^2
    q*(bn+2*q*b+q^2) ≤ b^2-bn := by
  dsimp
  have hq0 : 0 ≤ q := by linarith only [hqlo]
  have hq2 : q^2=1-q := by linarith only [hq]
  have hu0 : 0 ≤ u-1 := by linarith only [hu]
  have hF0 := mul_nonneg (sq_nonneg q)
    (mul_nonneg (show 0 ≤ u by linarith only [hu]) hu0)
  have hadiff := mul_nonneg (mul_nonneg hq0 ha)
    (show 0 ≤ u-1-2*a by linarith only [hahi])
  let K := (2-3*q)*u+q-2
  have hF : 0 ≤ q^2*u*(u-1)+2*a*(q^2*u-q*a-1) := by
    rw [hq2] at hF0 ⊢
    by_cases hK : 0 ≤ K
    · have hprod := mul_nonneg ha hK
      dsimp [K] at hprod
      nlinarith only [hF0,hadiff,hprod]
    · have hc0 : 0 ≤ 4-5*q := by linarith only [hqhi]
      have hc := mul_nonneg (show 0 ≤ u-3 by linarith only [hu]) hc0
      have hbr : 0 ≤ (4-5*q)*u+q-2 := by nlinarith only [hc,hqhi]
      have hend := mul_nonneg hu0 hbr
      have hcoeff := mul_nonneg (show 0 ≤ u-1-2*a by linarith only [hahi])
        (show 0 ≤ -K by linarith only [hK])
      dsimp [K] at hcoeff
      nlinarith only [hend,hcoeff,hadiff]
  have hL := mul_nonneg (show 0 ≤ 1+q by linarith only [hqlo])
    (show 0 ≤ a^2-L2 by linarith only [hL2])
  have hqu := congrArg (fun x : ℝ => x*u^2) hq
  have hqa := congrArg (fun x : ℝ => x*a*u) hq
  have hqq := congrArg (fun x : ℝ => x*q) hq
  have hqu1 := congrArg (fun x : ℝ => x*u) hq
  have hqa1 := congrArg (fun x : ℝ => x*a) hq
  have hqaa := congrArg (fun x : ℝ => x*a^2) hq
  nlinarith only [hF,hL,hq,hqu,hqa,hqq,hqu1,hqa1,hqaa]

theorem kernel_last_row_absorbs_next_numerator (q u a sQ P : ℝ)
    (hq : q^2+q=1) (hqlo : 3/5 ≤ q)
    (hu : 4 ≤ u) (ha : 2*a ≤ u-1)
    (hPq : P ≤ q^2) (hQ : u-q ≤ sQ)
    (hT : 0 ≤ u+q+a) :
    P*(u+q+a) ≤ sQ := by
  have hq0 : 0 ≤ q := by linarith only [hqlo]
  have hmul := mul_nonneg (show 0 ≤ q^2-P by linarith only [hPq]) hT
  have hcap := mul_nonneg (sq_nonneg q)
    (show 0 ≤ (u-1)/2-a by linarith only [ha])
  have hg := mul_nonneg (show 0 ≤ 3*q-1 by linarith only [hqlo])
    (show 0 ≤ u-4 by linarith only [hu])
  have hqu := congrArg (fun x : ℝ => x*u) hq
  have hqq := congrArg (fun x : ℝ => x*q) hq
  nlinarith only [hmul,hcap,hg,hQ,hq,hqu,hqq,hqlo]

theorem weighted_rows_and_last_LC_absorption (P a Ls Lnext last Tlast : ℝ)
    (hP : 0 ≤ P) (hLs : 0 ≤ Ls) (hLC : Lnext ≤ a*Ls)
    (hkernel : P*(Tlast+a) ≤ last) :
    P*(Ls*Tlast+Lnext) ≤ Ls*last := by
  have h1 := mul_nonneg hLs
    (show 0 ≤ last-P*(Tlast+a) by linarith only [hkernel])
  have h2 := mul_nonneg hP
    (show 0 ≤ a*Ls-Lnext by linarith only [hLC])
  nlinarith only [h1,h2]

#print axioms backward_geometric_LC_transport
#print axioms entire_finite_backward_integration
#print axioms entire_geometric_deficit_LC_bridge
#print axioms alternating_deficit_robust_budget
#print axioms first_robust_numerator_seed
#print axioms kernel_last_row_absorbs_next_numerator
#print axioms weighted_rows_and_last_LC_absorption

end BinaryCIInfiniteEntrance
