import Mathlib
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace StationaryTernaryReferenceC

def minor (H : ℕ → ℝ) (n : ℕ) := H (n+1)^2-H n*H (n+2)

theorem third_minor_recurrence (H : ℕ → ℝ)
    (hr : ∀ n,H (n+3)=H n+H (n+1)+H (n+2)) :
    ∀ n,minor H (n+3)= -minor H (n+2)-minor H (n+1)+minor H n := by
  intro n
  have h3 := hr n
  have h4 : H (n+4)=H (n+1)+H (n+2)+H (n+3) := by simpa [Nat.add_assoc] using hr (n+1)
  have h5 : H (n+5)=H (n+2)+H (n+3)+H (n+4) := by simpa [Nat.add_assoc] using hr (n+2)
  norm_num only [minor,Nat.add_assoc]
  simp only [h5,h4,h3]
  ring

theorem third_majorant (T M : ℕ → ℝ)
    (ht : ∀ n,T (n+3)=T n+T (n+1)+T (n+2))
    (hm : ∀ n,M (n+3)= -M (n+2)-M (n+1)+M n)
    (hb : ∀ n,n<3 → -T n ≤ M n ∧ M n ≤ T n) :
    ∀ n,-T n ≤ M n ∧ M n ≤ T n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n<3
      · exact hb n hn
      · have h0 := ih (n-3) (by omega)
        have h1 := ih (n-2) (by omega)
        have h2 := ih (n-1) (by omega)
        have ht1 := ht (n-3)
        have hm1 := hm (n-3)
        have e0 : n-3+3=n := by omega
        have e1 : n-3+1=n-2 := by omega
        have e2 : n-3+2=n-1 := by omega
        rw [e0,e1,e2] at ht1 hm1
        constructor <;> linarith

theorem third_positive (T : ℕ → ℝ)
    (ht : ∀ n,T (n+3)=T n+T (n+1)+T (n+2))
    (hb : ∀ n,n<3 → 0<T n) : ∀ n,0<T n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n<3
      · exact hb n hn
      · have h0 := ih (n-3) (by omega)
        have h1 := ih (n-2) (by omega)
        have h2 := ih (n-1) (by omega)
        have ht1 := ht (n-3)
        have e0 : n-3+3=n := by omega
        have e1 : n-3+1=n-2 := by omega
        have e2 : n-3+2=n-1 := by omega
        rw [e0,e1,e2] at ht1
        linarith

theorem whole_unperturbed_golden_reference_controls (q : ℝ) (H : ℕ → ℝ)
    (hq : q^2+q=1) (hp : 0 ≤ q)
    (h0 : H 0=1) (h1 : H 1= -q) (h2 : H 2=1-q)
    (hr : ∀ n,H (n+3)=H n+H (n+1)+H (n+2)) :
    ∀ n,6 ≤ n → 0<H (n-1) ∧ H n ≤ 2*H (n-1) ∧
      -H (n-1) ≤ H n^2-H (n-1)*H (n+1) ∧
      H n^2-H (n-1)*H (n+1) ≤ H (n-1) := by
  have hb : 3/5 ≤ q ∧ q ≤ 5/8 := by
    constructor
    · by_contra! h
      have hs := mul_self_le_mul_self hp (le_of_lt h)
      nlinarith
    · by_contra! h
      have hs := mul_self_le_mul_self (show (0:ℝ) ≤ 5/8 by norm_num) (le_of_lt h)
      nlinarith
  have h3 : H 3=2-2*q := by have h := hr 0;norm_num [h0,h1,h2] at h;linarith
  have h4 : H 4=3-4*q := by have h := hr 1;norm_num [h1,h2,h3] at h;linarith
  have h5 : H 5=6-7*q := by have h := hr 2;norm_num [h2,h3,h4] at h;linarith
  have h6 : H 6=11-13*q := by have h := hr 3;norm_num [h3,h4,h5] at h;linarith
  have h7 : H 7=20-24*q := by have h := hr 4;norm_num [h4,h5,h6] at h;linarith
  have h8 : H 8=37-44*q := by have h := hr 5;norm_num [h5,h6,h7] at h;linarith
  have h9 : H 9=68-81*q := by have h := hr 6;norm_num [h6,h7,h8] at h;linarith
  let T : ℕ → ℝ := fun n => H (n+5)
  let A : ℕ → ℝ := fun n => 2*H (n+5)-H (n+6)
  let M : ℕ → ℝ := fun n => minor H (n+5)
  have ht : ∀ n,T (n+3)=T n+T (n+1)+T (n+2) := by
    intro n
    dsimp [T]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr (n+5)
  have ha : ∀ n,A (n+3)=A n+A (n+1)+A (n+2) := by
    intro n
    dsimp [A]
    have he := hr (n+5)
    have hf := hr (n+6)
    norm_num only [Nat.add_assoc] at he hf ⊢
    linear_combination 2*he-hf
  have hm : ∀ n,M (n+3)= -M (n+2)-M (n+1)+M n := by
    intro n
    dsimp [M]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using third_minor_recurrence H hr (n+5)
  have htpos : ∀ n,0<T n := third_positive T ht (by
    intro n hn
    interval_cases n <;> norm_num [T,h5,h6,h7] <;> linarith [hb.2])
  have hapos : ∀ n,0<A n := third_positive A ha (by
    intro n hn
    interval_cases n <;> norm_num [A,h5,h6,h7,h8] <;> linarith [hb.2])
  have hbase : ∀ n,n<3 → -T n ≤ M n ∧ M n ≤ T n := by
    intro n hn
    interval_cases n <;> norm_num [T,M,minor,h5,h6,h7,h8,h9] <;> constructor <;> nlinarith [hq,hb.1,hb.2]
  have hbound := third_majorant T M ht hm hbase
  intro n hn
  have hP := htpos (n-6)
  have hA := hapos (n-6)
  have hM := hbound (n-6)
  have e0 : n-6+5=n-1 := by omega
  have e1 : n-6+6=n := by omega
  have e2 : n-1+1=n := by omega
  have e3 : n-1+2=n+1 := by omega
  dsimp [T] at hP
  dsimp [A] at hA
  dsimp [T,M,minor] at hM
  rw [e0] at hP
  rw [e0,e1] at hA
  rw [e0,e2,e3] at hM
  exact ⟨hP,by linarith,hM.1,hM.2⟩

theorem complete_both_left_golden_residual_entrances (l r T U V W : ℝ)
    (hl : l ≤ 2) (hr : 7 ≤ r) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hTU : U ≤ 2*T) (hUV : V ≤ 2*U)
    (hM0 : -T ≤ U^2-T*V) (hM1 : -U ≤ V^2-U*W)
    (hnext : (r^2+5*r+10)/2-l*(r+2) ≤ W) :
    0 ≤ (U-1)^2-T*(V-(r+2-l)) ∧
    0 ≤ (V-(r+2-l))^2-(U-1)*(W-((r^2+5*r+10)/2-l*(r+2))) := by
  let b := r+2-l
  let c := (r^2+5*r+10)/2-l*(r+2)
  have hb : 5 ≤ b := by dsimp [b];linarith
  have hc : 0 ≤ c-4*b-1 := by
    have hid : c-4*b-1=r*(r-7)/2+(2-l)*(r-2) := by dsimp [b,c];ring
    rw [hid]
    have h1 := mul_nonneg (show 0 ≤ r by linarith) (show 0 ≤ r-7 by linarith)
    have h2 := mul_nonneg (show 0 ≤ 2-l by linarith) (show 0 ≤ r-2 by linarith)
    linarith
  have h10 := mul_nonneg hT (show 0 ≤ b-5 by linarith)
  have h11 := mul_nonneg hU hc
  have h12 := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 2*U-V by linarith)
  have hid : (V-b)^2-(U-1)*(W-c)
      =(V^2-U*W)-2*b*V+b^2+U*c+(W-c) := by ring
  change 0 ≤ (U-1)^2-T*(V-b) ∧ 0 ≤ (V-b)^2-(U-1)*(W-c)
  constructor
  · nlinarith
  · have hn : 0 ≤ W-c := by dsimp [c];linarith
    nlinarith [sq_nonneg b]

theorem whole_terminal_budget_inherited_from_forward_CI (q r tau : ℝ)
    (hq : 0 ≤ q) (ht : 0 ≤ tau)
    (hOld : 2*(1+q+q*r)*tau ≤ (1+q)^2) :
    2*(1+q+q*(r-1))*tau ≤ (1+q)^2 := by
  have h := mul_nonneg hq ht
  nlinarith

theorem all_two_ended_window_read_guards (r n : ℕ)
    (_hr : 6 ≤ r) (hn : r+6 ≤ n) (hu : n ≤ 3*r+1) :
    r+2 ≤ n-4 ∧ n-1 ≤ 3*r ∧ n ≤ 3*r ∨
      (r+2 ≤ n-4 ∧ n-1=3*r ∧ n=3*r+1) := by omega

#print axioms whole_unperturbed_golden_reference_controls
#print axioms complete_both_left_golden_residual_entrances
#print axioms whole_terminal_budget_inherited_from_forward_CI
#print axioms all_two_ended_window_read_guards
end StationaryTernaryReferenceC
