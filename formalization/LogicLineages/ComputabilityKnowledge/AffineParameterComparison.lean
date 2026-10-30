module

public import LogicLineages.ComputabilityKnowledge.AffineParameterSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.UnaryComparison

@[expose] public section

/-! Exact affine-parameter comparison consumer from paper02 cor:consumers.
The valuation is the original unclamped ai*n+bi; positivity comes from the
already proved coefficient-domain theorem. These programs compose the actual
guarded prefix compiler and actual unary least-counterexample program. This
module does not assert the separate WW vector/admissibility/norm clauses. -/
namespace LogicLineages.ComputabilityKnowledge.AffineParameterComparison

open PositiveExpression AffineParameterSubstitution

def valuation (d : Nat) (as bs : List Nat) (h : Admissible d as bs) (n : PosNat) : Fin d → PosNat :=
  fun i => ⟨as.getD i.val 0 * (n : Nat) + bs.getD i.val 0,
    AffineParameterSubstitutionProof.positiveCoordinates d as bs h n i⟩

def Holds (weak : Bool) (d : Nat) (as bs : List Nat) (h : Admissible d as bs)
    (a b : Expr (Fin d)) (n : PosNat) : Prop :=
  if weak then a.eval (valuation d as bs h n) ≤ b.eval (valuation d as bs h n)
  else a.eval (valuation d as bs h n) < b.eval (valuation d as bs h n)

def resultCode (weak : Bool) (d : Nat) (as bs a b : List Nat) : Option (Option Nat) := do
  let a' ← AffineParameterSubstitution.compileCode d as bs a
  let b' ← AffineParameterSubstitution.compileCode d as bs b
  UnaryComparison.resultCode weak a' b'

def decisionCode (weak : Bool) (d : Nat) (as bs a b : List Nat) : Option Bool :=
  (resultCode weak d as bs a b).map Option.isNone

end LogicLineages.ComputabilityKnowledge.AffineParameterComparison
