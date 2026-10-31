module
public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear
open FirstOrder Language

/-- Intrinsically finite-arity integer affine data. There is no nonlinear
variable multiplication or out-of-range/default variable lookup. -/
structure Affine (n : Nat) where
  constant : Int
  coeff : Fin n → Int

namespace Affine

def eval {n : Nat} (t : Affine n) (v : Fin n → Int) : Int :=
  t.constant + ∑ i, t.coeff i * v i

def const {n : Nat} (z : Int) : Affine n := ⟨z, fun _ => 0⟩
def var {n : Nat} (i : Fin n) : Affine n := ⟨0, fun j => if i = j then 1 else 0⟩
def add {n : Nat} (s t : Affine n) : Affine n :=
  ⟨s.constant + t.constant, fun i => s.coeff i + t.coeff i⟩
def scale {n : Nat} (z : Int) (t : Affine n) : Affine n :=
  ⟨z * t.constant, fun i => z * t.coeff i⟩

/-- Literal recursive compilation of the actual pinned (0,1,+) term syntax. -/
def ofTerm {n : Nat} : Language.presburger.Term (Fin n) → Affine n
  | .var i => var i
  | .func .zero _ => const 0
  | .func .one _ => const 1
  | .func .add ts => add (ofTerm (ts 0)) (ofTerm (ts 1))

/-- Keep the prefix coordinates; the newest bound variable is last, matching
Mathlib's `BoundedFormula.Realize`/`Fin.snoc` binder convention. -/
def dropLast {n : Nat} (t : Affine (n + 1)) : Affine n :=
  ⟨t.constant, fun i => t.coeff i.castSucc⟩
def lastCoeff {n : Nat} (t : Affine (n + 1)) : Int := t.coeff (Fin.last n)
def substLast {n : Nat} (t : Affine (n + 1)) (s : Affine n) : Affine n :=
  add (dropLast t) (scale (lastCoeff t) s)

end Affine
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinear
