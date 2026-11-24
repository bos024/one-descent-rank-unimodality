import Mathlib

namespace FastListPolynomial

noncomputable def poly : List ℤ → Polynomial ℤ
  | [] => 0
  | a::p => Polynomial.C a+Polynomial.X*poly p

def add : List ℤ → List ℤ → List ℤ
  | [],q => q
  | a::p,[] => a::p
  | a::p,b::q => (a+b)::add p q

def mul : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | a::p,q => add (q.map (fun b => a*b)) (0::mul p q)

theorem poly_add (p q : List ℤ) : poly (add p q)=poly p+poly q := by
  induction p generalizing q with
  | nil => simp [add,poly]
  | cons a p ih =>
    cases q with
    | nil => simp [add,poly]
    | cons b q =>
      simp only [add,poly,ih,Polynomial.C_add]
      ring

theorem poly_scale (a : ℤ) (p : List ℤ) :
    poly (p.map (fun b => a*b))=Polynomial.C a*poly p := by
  induction p with
  | nil => simp [poly]
  | cons b p ih =>
    simp only [List.map_cons,poly,ih,Polynomial.C_mul]
    ring

theorem poly_mul (p q : List ℤ) : poly (mul p q)=poly p*poly q := by
  induction p with
  | nil => simp [mul,poly]
  | cons a p ih =>
    rw [mul,poly_add,poly_scale,poly,ih,poly]
    simp only [Polynomial.C_0,zero_add]
    ring

#print axioms poly_add
#print axioms poly_scale
#print axioms poly_mul
end FastListPolynomial
