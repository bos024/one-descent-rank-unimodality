import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 131072
namespace AllRankHeadFlagBoundary

def partitions : ℕ → ℕ → List (List ℕ)
  | 0,n => if n=0 then [[]] else []
  | t+1,n => (List.range (n/(t+1)+1)).flatMap fun k =>
      (partitions t (n-k*(t+1))).map fun p => p++List.replicate k (t+1)

structure Context where
  k : ℕ
  c : ℕ
  g : ℕ
  s : ℤ
  j : ℕ

def Context.b (v : Context) : ℕ := ((v.c:ℤ)+v.s).toNat

def contexts : List Context :=
  ([5,6,7,8] : List ℕ).flatMap fun (k : ℕ) =>
    (List.range 41).flatMap fun (c : ℕ) =>
      if k*(k-1) ≤ 2*c then
        (List.range 7).flatMap fun (g : ℕ) =>
          if g ≤ k-2 then
            (List.range (2*g+2)).flatMap fun (i : ℕ) =>
              let s:=(i:ℤ)-(g:ℤ)-1
              if 0<(c:ℤ)+s then
                ((List.range 7).filter (fun (j : ℕ) => decide (2 ≤ j ∧ j ≤ g ∧ 2*(j:ℤ) ≤ (g:ℤ)+s+1))).map
                  (fun j => ⟨k,c,g,s,j⟩)
              else []
          else []
      else []

def words (v : Context) : List (List ℕ) :=
  (List.range 5).flatMap fun E =>
    let b:=v.b
    if E+1 ≤ b ∧ (b-E-1)%2=0 then
      let h:=(b-E-1)/2
      if b-h<v.k+2*v.j-2 then
        (List.range (E+1)).flatMap fun A =>
          ((partitions 4 (E-A)).filter (fun P => decide (P.length ≤ h))).map fun P =>
            List.replicate (A+1) 1++List.replicate (h-P.length) 2++P.map (fun x => x+2)
      else []
    else []

def rows : List (Context × List ℕ) :=
  contexts.flatMap fun v => (words v).map fun Y => (v,Y)

def coeff (p : List ℤ) (n : ℕ) : ℤ := p[n]?.getD 0

def window (p : List ℤ) (t : ℕ) : List ℤ :=
  (List.range (p.length+t-1)).map fun n =>
    ((List.range t).map fun j => if j ≤ n then coeff p (n-j) else 0).sum

def forward (w : List ℕ) : List ℤ := w.foldl (fun p t => 1::window p t) [1]

def check (row : Context × List ℕ) : Bool :=
  let (v,Y):=row
  let q:=(forward Y).reverse
  let delta:=coeff q v.j-2*coeff q (v.j-1)+coeff q (v.j-2)
  decide (Y.sum=v.b) && (if 0<delta then decide (delta+1 ≤ coeff q (v.k+v.j-2)) else true)

theorem complete_small_boundary : rows.all check=true := by decide +kernel
theorem exact_profile_count : rows.length=73 := by decide +kernel

def diagonalCheck (row : Context × List ℕ) : Bool :=
  let (v,Y):=row
  let F:=forward Y
  let q:=F.reverse
  let r : ℤ := v.s-(v.j:ℤ)
  let forwardValue:=if 0 ≤ r then coeff F r.toNat else 0
  let delta:=coeff q v.j-2*coeff q (v.j-1)+coeff q (v.j-2)
  decide (delta ≤ coeff q (v.k+v.j-2)-forwardValue)

theorem complete_small_boundary_diagonal : rows.all diagonalCheck=true := by decide +kernel

theorem degree_failure_finite_domain (k c g s b h m j : ℤ)
    (hk : 5 ≤ k) (hmass : k*(k-1) ≤ 2*c)
    (hg : 0 ≤ g ∧ g ≤ k-2) (hs : s ≤ g)
    (hb : b=c+s) (hh : 0 ≤ h ∧ 2*h ≤ b-1) (hm : m=b-h)
    (hj : 2 ≤ j ∧ 2*j ≤ g+s+1) (hfail : m<k+2*j-2) :
    k ≤ 8 ∧ 0 ≤ c ∧ c ≤ 40 ∧ g ≤ 6 ∧
    -g-1 ≤ s ∧ j ≤ g ∧ 1 ≤ b ∧ b ≤ 33 ∧
    0 ≤ b-2*h-1 ∧ b-2*h-1 ≤ 4 := by
  have hc5 : 5*k-15 ≤ c := by
    by_cases he : k=5
    · subst k
      norm_num at hmass ⊢
      omega
    · have hk6 : 6 ≤ k := by omega
      have hp : 0 ≤ (k-5)*(k-6) := mul_nonneg (by omega) (by omega)
      nlinarith
  have hk8 : k ≤ 8 := by
    by_contra h
    have hk9 : 9 ≤ k := by omega
    have hp : 0 ≤ (k-2)*(k-9) := mul_nonneg (by omega) (by omega)
    have hc9 : 5*k-9 ≤ c := by nlinarith
    omega
  omega

#print axioms complete_small_boundary
#print axioms exact_profile_count
#print axioms complete_small_boundary_diagonal
#print axioms degree_failure_finite_domain
end AllRankHeadFlagBoundary
