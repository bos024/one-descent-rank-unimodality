import Mathlib

namespace DepthSlackTransport
open Finset

/-- The mass of a tail of the depth distribution increases with completed weight. -/
theorem tail_minor {ι : Type*} (lo hi : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ lo, ∀ j ∈ hi, p i*q j ≥ q i*p j) :
    (∑ j ∈ hi, p j)*((∑ i ∈ lo, q i)+(∑ j ∈ hi, q j)) ≤ (∑ j ∈ hi, q j)*((∑ i ∈ lo, p i)+(∑ j ∈ hi, p j)) := by
  have hpair : ∑ i ∈ lo, ∑ j ∈ hi, q i*p j ≤ ∑ i ∈ lo, ∑ j ∈ hi, p i*q j :=
    Finset.sum_le_sum fun i h => Finset.sum_le_sum fun j hj => hp i h j hj
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hpair
  linarith

/-- The transitions that preserve weight and that increase it by one. -/
theorem transition_nonneg (a b u v : ℝ) (ha : 0<a) (hab : a ≤ b)
    (hu : 0 ≤ u) (hr : b*v ≤ a*u) :
    0 ≤ u/b-v/a ∧ 0 ≤ u/a-u/b := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  constructor
  · apply sub_nonneg.mpr
    rw [div_le_div_iff₀ ha hb]
    nlinarith
  · apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left hu ha hab

theorem split_old (a b u v : ℝ) :
    (u/b-v/a)+(u/a-u/b)=(u-v)/a := by ring

theorem receive_new (a b u v : ℝ) :
    (u/b-v/a)+(v/a-v/b)=(u-v)/b := by ring

theorem last_edge (a b : ℝ) (ha : a≠0) :
    a/a-a/b=(b-a)/b ∨ b=0 := by
  by_cases hb : b=0
  · exact Or.inr hb
  · left
    field_simp

/-- Summing a stay/move transport, including its two end points. -/
theorem edge_transport (n : ℕ) (stay move old now : ℕ → ℝ)
    (hs : ∀ i<n, 0 ≤ stay i) (hm : ∀ i<n, 0 ≤ move i)
    (hfixed : ∀ i<n, old i ≤ now i) (hnext : ∀ i<n, old i ≤ now (i+1)) :
    (∑ i ∈ range n, (stay i+move i)*old i) ≤ ∑ i ∈ range n, (stay i*now i+move i*now (i+1)) := by
  apply Finset.sum_le_sum
  intro i hi
  have h := Finset.mem_range.mp hi
  have h1 := mul_le_mul_of_nonneg_left (hfixed i h) (hs i h)
  have h2 := mul_le_mul_of_nonneg_left (hnext i h) (hm i h)
  linarith

theorem sum_receive (n : ℕ) (stay move test : ℕ → ℝ) :
    (∑ i ∈ range (n+1), (stay i*test i+move i*test (i+1))) =
    stay 0*test 0 +
    (∑ i ∈ range n, (move i+stay (i+1))*test (i+1)) + move n*test (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

theorem loss_closes_LC (prev cur nxt lossPrev lossNow : ℝ)
    (hpre : cur=2*prev-lossPrev) (hnow : nxt=2*cur-lossNow)
    (hc : lossPrev*cur ≤ lossNow*prev) :
    prev*nxt ≤ cur^2 := by
  rw [hnow]
  have hp := congrArg (fun z : ℝ => z*cur) hpre
  nlinarith only [hc,hp]

theorem LC_of_conditional_loss (C L : ℕ → ℝ)
    (rec : ∀ n, C (n+1)=2*C n-L n)
    (step : ∀ n, (∀ i<n, C i*C (i+2) ≤ (C (i+1))^2) →
      L n*C (n+1) ≤ L (n+1)*C n) :
    ∀ n, C n*C (n+2) ≤ (C (n+1))^2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    exact loss_closes_LC _ _ _ _ _ (rec n) (rec (n+1)) (step n ih)

theorem complement_density (x y lx ly : ℝ) (h : lx*y ≤ ly*x) :
    (y-ly)*x ≤ (x-lx)*y := by linarith

theorem deepest_layer (S : Finset ℕ) (a b : ℕ → ℝ) (x y : ℝ)
    (h : ∀ i∈S, x*b i ≤ y*a i) :
    ((∑ i∈S, b i)+y)*(∑ i∈S, a i) ≥
    ((∑ i∈S, a i)+x)*(∑ i∈S, b i) := by
  have h0 := Finset.sum_le_sum h
  simp only [← Finset.mul_sum] at h0
  nlinarith

theorem bridge (d e u v cPrev cCur gPrev gCur : ℝ)
    (hu : 0<u) (hc : 0<cPrev) (hd : 0 ≤ d)
    (hg : 0 ≤ gPrev) (h1 : e*u ≤ d*v) (h2 : v*cPrev ≤ u*cCur)
    (h3 : cCur*gPrev ≤ cPrev*gCur) :
    e*gPrev ≤ d*gCur := by
  have h12 : e*cPrev ≤ d*cCur := by
    apply (le_of_mul_le_mul_right ?_ hu)
    calc
      e*cPrev*u = (e*u)*cPrev := by ring
      _ ≤ d*v*cPrev := mul_le_mul_of_nonneg_right h1 hc.le
      _ ≤ d*cCur*u := by nlinarith [mul_le_mul_of_nonneg_left h2 hd]
  apply (le_of_mul_le_mul_right ?_ hc)
  calc
    e*gPrev*cPrev = (e*cPrev)*gPrev := by ring
    _ ≤ d*cCur*gPrev := mul_le_mul_of_nonneg_right h12 hg
    _ ≤ d*gCur*cPrev := by nlinarith [mul_le_mul_of_nonneg_left h3 hd]

/-- Direct clipped finite-padding transfer through a positive intermediate scale. -/
theorem padding_transfer (d e a b u v : ℝ) (ha : 0<a)
    (hu : 0 ≤ u) (hd : 0 ≤ d) (h1 : e*a ≤ d*b) (h2 : b*u ≤ a*v) :
    e*u ≤ d*v := by
  apply (le_of_mul_le_mul_right ?_ ha)
  calc
    e*u*a = (e*a)*u := by ring
    _ ≤ (d*b)*u := mul_le_mul_of_nonneg_right h1 hu
    _ ≤ d*v*a := by nlinarith [mul_le_mul_of_nonneg_left h2 hd]


noncomputable def expect (S : ℕ → ℝ) (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, (S (k+1)-S k)/S m*f k

theorem budget_step (m : ℕ) (S f g : ℕ → ℝ) (h0 : S 0=0)
    (ha : 0<S (m+1)) (hab : S (m+1) ≤ S (m+2))
    (hpos : ∀ k ≤ m, 0 ≤ S (k+1))
    (hc : ∀ k ≤ m, S (m+2)*S k ≤ S (m+1)*S (k+1))
    (hg : ∀ k ≤ m, f k ≤ g k ∧ f k ≤ g (k+1)) :
    expect S (m+1) f ≤ expect S (m+2) g := by
  let stay (k : ℕ) := S (k+1)/S (m+2)-S k/S (m+1)
  let move (k : ℕ) := S (k+1)/S (m+1)-S (k+1)/S (m+2)
  have hn (k : ℕ) (hk : k < m+1) : 0 ≤ stay k ∧ 0 ≤ move k :=
    transition_nonneg _ _ _ _ ha hab (hpos k (by omega)) (hc k (by omega))
  have hb := edge_transport (m+1) stay move f g (fun i hi => (hn i hi).1)
    (fun i hi => (hn i hi).2) (fun i hi => (hg i (by omega)).1)
    (fun i hi => (hg i (by omega)).2)
  have hold (k : ℕ) : stay k+move k=(S (k+1)-S k)/S (m+1) := by dsimp [stay,move]; ring
  simp_rw [hold] at hb
  rw [sum_receive] at hb
  have hmid (k : ℕ) : move k+stay (k+1)=(S (k+2)-S (k+1))/S (m+2) := by
    dsimp [move,stay]
    ring
  simp_rw [hmid] at hb
  have hstart : stay 0=(S 1-S 0)/S (m+2) := by simp [stay,h0]
  have hlast : move m=(S (m+2)-S (m+1))/S (m+2) := by
    dsimp [move]
    have hbpos := lt_of_lt_of_le ha hab
    field_simp
  rw [hstart,hlast] at hb
  unfold expect
  rw [Finset.sum_range_succ (n:=m+1),Finset.sum_range_succ' (f:=fun i => (S (i+1)-S i)/S (m+2)*g i) (n:=m)]
  linarith only [hb]

theorem ratio_chain (C : ℕ → ℝ) (hp : ∀ i, 0<C i) (n : ℕ)
    (hc : ∀ i<n, C i*C (i+2) ≤ (C (i+1))^2) :
    ∀ k ≤ n, C (n+1)/C n ≤ C (k+1)/C k := by
  induction n with
  | zero => intro k hk; have := Nat.eq_zero_of_le_zero hk; subst k; rfl
  | succ n ih =>
    have hadj : C (n+2)/C (n+1) ≤ C (n+1)/C n := by
      rw [div_le_div_iff₀ (hp _) (hp _)]
      nlinarith only [hc n (by omega)]
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with e | e
    · subst k; rfl
    · exact hadj.trans (ih (fun i hi => hc i (by omega)) k (by omega))

def before (C : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | n+1 => C n
noncomputable def hit (C : ℕ → ℝ) (phi : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  expect (before C) (n+1) (fun k => phi k (n-k))

theorem ordered_expectation (C : ℕ → ℝ) (phi : ℕ → ℕ → ℝ)
    (hp : ∀ i, 0<C i) (hm : Monotone C)
    (hx : ∀ i s, phi i s ≤ phi (i+1) s) (hy : ∀ i s, phi i s ≤ phi i (s+1))
    (n : ℕ) (hLC : ∀ i<n, C i*C (i+2) ≤ (C (i+1))^2) :
    hit C phi n ≤ hit C phi (n+1) := by
  apply budget_step n (before C) _ _ rfl (hp n) (hm (Nat.le_succ n))
  · intro k hk; exact (hp k).le
  · intro k hk
    cases k with
    | zero => simpa only [before,mul_zero] using mul_nonneg (hp n).le (hp 0).le
    | succ k =>
      change C (n+1)*C k ≤ C n*C (k+1)
      have h := ratio_chain C hp n hLC k (by omega)
      rw [div_le_div_iff₀ (hp _) (hp _)] at h
      linarith only [h]
  · intro k hk
    constructor
    · rw [show n+1-k=n-k+1 by omega]
      exact hy _ _
    · rw [show n+1-(k+1)=n-k by omega]
      exact hx _ _

/-- An actual loss fraction is the mean of a function increasing in both coordinates. -/
theorem logconcave_and_all_thresholds (C : ℕ → ℝ) (birth : ℕ → ℕ → ℝ)
    (hp : ∀ i, 0<C i) (hm : Monotone C)
    (hx : ∀ i s, birth i s ≤ birth (i+1) s) (hy : ∀ i s, birth i s ≤ birth i (s+1))
    (rec : ∀ n, C (n+1)/C n=2-hit C birth n) :
    (∀ n, C n*C (n+2) ≤ (C (n+1))^2) ∧
    ∀ phi : ℕ → ℕ → ℝ, (∀ i s, phi i s ≤ phi (i+1) s) →
      (∀ i s, phi i s ≤ phi i (s+1)) → ∀ n, hit C phi n ≤ hit C phi (n+1) := by
  have hLC : ∀ n, C n*C (n+2) ≤ (C (n+1))^2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have h := ordered_expectation C birth hp hm hx hy n ih
      have qr : C (n+2)/C (n+1) ≤ C (n+1)/C n := by
        rw [rec (n+1),rec n]
        linarith only [h]
      rw [div_le_div_iff₀ (hp _) (hp _)] at qr
      nlinarith only [qr]
  exact ⟨hLC, fun phi a b n => ordered_expectation C phi hp hm a b n (fun i _ => hLC i)⟩


/-- Unrestricted coefficient readings, including a vanishing earlier difference. -/
theorem all_delays (C D G : ℕ → ℝ) (hC : ∀ i, 0<C i) (hD : ∀ i, 0 ≤ D i)
    (hG : ∀ i, 0<G i) (lc : ∀ i, C i*C (i+2) ≤ (C (i+1))^2)
    (left : ∀ i, D (i+1)*C i ≤ D i*C (i+1))
    (right : ∀ i, G i*C (i+1) ≤ G (i+1)*C i)
    (n k : ℕ) (hk : k ≤ n) : D (n+1)*G k ≤ D n*G (k+1) := by
  have hlow : D (n+1) ≤ D n*(C (n+1)/C n) := by
    rw [← mul_div_assoc,le_div_iff₀ (hC _)]
    exact left n
  have hchain := ratio_chain C hC n (fun i _ => lc i) k hk
  have hhigh : C (k+1)/C k ≤ G (k+1)/G k := by
    rw [div_le_div_iff₀ (hC _) (hG _)]
    nlinarith only [right k]
  have hlast := hlow.trans (mul_le_mul_of_nonneg_left (hchain.trans hhigh) (hD n))
  rw [← mul_div_assoc,le_div_iff₀ (hG _)] at hlast
  exact hlast

theorem all_finite_padding_delays (C A D G : ℕ → ℝ)
    (hC : ∀ i, 0<C i) (hA : ∀ i, 0 ≤ A i) (hD : ∀ i, 0 ≤ D i)
    (dom : ∀ i, D i ≤ A i) (hG : ∀ i, 0<G i)
    (lc : ∀ i, C i*C (i+2) ≤ (C (i+1))^2)
    (threshold : ∀ i, A (i+1)*C i ≤ A i*C (i+1))
    (pad : ∀ i, D (i+1)*A i ≤ D i*A (i+1))
    (endMass : ∀ i, G i*C (i+1) ≤ G (i+1)*C i)
    (n k : ℕ) (hk : k ≤ n) : D (n+1)*G k ≤ D n*G (k+1) := by
  apply all_delays C D G hC hD hG lc _ endMass n k hk
  intro i
  by_cases h : 0<A i
  · exact padding_transfer _ _ _ _ _ _ h (hC i).le (hD i) (pad i) (threshold i)
  · have ha : A i=0 := by linarith only [h,hA i]
    have hprod : A (i+1)*C i ≤ 0 := by simpa [ha] using threshold i
    have han : A (i+1) ≤ 0 := nonpos_of_mul_nonpos_left hprod (hC i)
    have hd0 : D (i+1)=0 := by linarith only [han,dom (i+1),hD (i+1)]
    rw [hd0,zero_mul]
    exact mul_nonneg (hD i) (hC (i+1)).le

end DepthSlackTransport
#print axioms DepthSlackTransport.tail_minor
#print axioms DepthSlackTransport.transition_nonneg
#print axioms DepthSlackTransport.split_old
#print axioms DepthSlackTransport.receive_new
#print axioms DepthSlackTransport.last_edge
#print axioms DepthSlackTransport.edge_transport
#print axioms DepthSlackTransport.sum_receive
#print axioms DepthSlackTransport.loss_closes_LC
#print axioms DepthSlackTransport.LC_of_conditional_loss
#print axioms DepthSlackTransport.complement_density
#print axioms DepthSlackTransport.deepest_layer
#print axioms DepthSlackTransport.bridge
#print axioms DepthSlackTransport.padding_transfer
#print axioms DepthSlackTransport.budget_step
#print axioms DepthSlackTransport.ratio_chain
#print axioms DepthSlackTransport.ordered_expectation
#print axioms DepthSlackTransport.logconcave_and_all_thresholds
#print axioms DepthSlackTransport.all_delays
#print axioms DepthSlackTransport.all_finite_padding_delays