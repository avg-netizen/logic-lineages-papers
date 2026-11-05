module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitGadgetDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitGadgetTargets
open Polynomial CircuitLinear Narendran

/-- The same four global unknowns occur in every equation, including indices
that happen to repeat. Scalar parameters are explicit natural constants. -/
def SquareRowsMeaning : Prop := ∀ (p : Nat → NPolynomial) (u v aux U V : Nat),
  p u=C U → p v=C V →
  (RowsSolve p (squareRows u v aux) ↔ SquareGadget U V (fun i : Fin 4 => p (aux+i.val)))

/-- Exact five polynomial gadget rows and one scalar sum row, with the same
nine global witnesses. No geometric witness is required to be constant. -/
def ConstantRowsMeaning : Prop := ∀ (p : Nat → NPolynomial) (n aux : Nat),
  RowsSolve p (constantRows n aux) ↔
    ConstantGadget (p aux) (fun i : Fin 7 => p (aux+2+i.val)) ∧
      (∑ i : Fin n, p i.val) + p (aux+1) = p aux

def ConstantRowsForceScalars : Prop := ∀ (p : Nat → NPolynomial) (n aux : Nat),
  RowsSolve p (constantRows n aux) → ∀ i, i<n → ∃ k : Nat, p i=C k

def TriangularIdentity : Prop := ∀ n : Nat, 2*triangularNat n+n=n^2

def TriangularAddition : Prop := ∀ x y : Nat,
  triangularNat (x+y)=triangularNat x+triangularNat y+x*y

def TriangularMultiplication : Prop := ∀ x y out v1 v2 v3 : Nat,
  2*v1+x=x^2 → 2*v2+y=y^2 → 2*v3+(x+y)=(x+y)^2 →
  v3=v1+v2+out → out=x*y

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitGadgetTargets
