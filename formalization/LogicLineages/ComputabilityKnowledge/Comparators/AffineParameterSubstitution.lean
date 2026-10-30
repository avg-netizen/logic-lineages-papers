module

public import LogicLineages.ComputabilityKnowledge.AffineParameterSubstitution

@[expose] public section

/-! Source affine-substitution compiler supplier for paper02 cor:consumers.
Literal source grammar, zero-summand cases, nonnegative integer coefficients,
positive coordinates, actual depth, exact parser/domain, and genuine uniform
programs are retained. Full WW vector/norm conclusions are not asserted. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterSubstitution

open PositiveExpression CircuitReduction FiniteComparisonEnumeration
open LogicLineages.ComputabilityKnowledge.AffineParameterSubstitution

def CoordinateSyntax : Prop :=
  ∀ (a b : Nat), (coordinateExpr a b).depth = 0 ∧
    coordinateCode a b = encodeExpr ((coordinateExpr a b).rename Fin.val) ∧
    ∀ n : PosNat, 0 < a + b → (coordinateExpr a b).eval (fun _ => n) = a * (n : Nat) + b

def PositiveCoordinates : Prop :=
  ∀ (d : Nat) (as bs : List Nat), Admissible d as bs →
    ∀ (n : PosNat) (i : Fin d), 0 < as.getD i.val 0 * (n : Nat) + bs.getD i.val 0

def LiteralSubstitution : Prop :=
  ∀ (d : Nat) (as bs : List Nat) (e : Expr (Fin d)), Admissible d as bs →
    (substitute as bs e).depth = e.depth ∧
    ∀ (n : PosNat) (ρ : Fin d → PosNat),
      (∀ i, (ρ i : Nat) = as.getD i.val 0 * (n : Nat) + bs.getD i.val 0) →
      (substitute as bs e).eval (fun _ => n) = e.eval ρ

def CoefficientDomain : Prop :=
  ∀ (d : Nat) (as bs : List Nat), coefficientsOK d as bs = true ↔ Admissible d as bs

def LiteralCompiler : Prop :=
  ∀ (d : Nat) (as bs : List Nat) (e : Expr (Fin d)), Admissible d as bs →
    compileCode d as bs (encodeExpr (e.rename Fin.val)) =
      some (encodeExpr ((substitute as bs e).rename Fin.val))

def ExactRawDomain : Prop :=
  ∀ (d : Nat) (as bs raw : List Nat),
    (compileCode d as bs raw).isSome = (coefficientsOK d as bs && (decodeExpr d raw).isSome)

def OutputSourceSyntax : Prop :=
  ∀ (d : Nat) (as bs raw out : List Nat), compileCode d as bs raw = some out →
    ∃ e : Expr (Fin 1), out = encodeExpr (e.rename Fin.val)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × List Nat => copiesCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => coordinateCode p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => coefficientsOK p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat × List Nat => compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := CoordinateSyntax ∧ PositiveCoordinates ∧ LiteralSubstitution ∧
  CoefficientDomain ∧ LiteralCompiler ∧ ExactRawDomain ∧ OutputSourceSyntax ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterSubstitution
