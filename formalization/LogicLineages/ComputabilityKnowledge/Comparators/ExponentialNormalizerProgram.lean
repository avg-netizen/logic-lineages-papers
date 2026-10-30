module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram

@[expose] public section

/-! Full paper-02 effective-normalization target. The actual program consumes
the unchanged literal prefix codec. It must compute the exact source depth,
produce a canonical code for the existing normal form, reject exactly the
existing decoder's malformed/out-of-arity inputs, and possess actual uniform
primitive-recursive certificates. The final source conclusion includes every
positive tuple and the actual well-formed hereditary-map predicate.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizerProgram

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open ExponentialNormalizer FiniteComparisonEnumeration CircuitReduction
open LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgram

def LiteralCompilation : Prop :=
  ∀ (d H : Nat) (e : Expr (Fin d)),
    compileAt d H (encodeExpr (e.rename Fin.val)) =
      some ((expressionRow d H e).getD H 0)

def RowRepresentation : Prop :=
  ∀ (d H : Nat) (e : Expr (Fin d)),
    (expressionRow d H e).length = H + 1 ∧
    ∀ h ≤ H,
      CodeCanonical d h ((expressionRow d H e).getD h 0) ∧
      formDecode d h ((expressionRow d H e).getD h 0) = normalizeAt e h

def ExactDepth : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)),
    depthCode d (encodeExpr (e.rename Fin.val)) = some e.depth

def RawDomain : Prop :=
  ∀ (d H : Nat) (raw : List Nat),
    (compileAt d H raw).isSome = (decodeExpr d raw).isSome ∧
    (depthCode d raw).isSome = (decodeExpr d raw).isSome

def ActualPrimitivePrograms : Prop :=
  Primrec (fun p : Nat × Nat × List Nat => compileAt p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat => depthCode p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => normalizeCode p.1 p.2)

def FullEffectiveNormalization : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)), ∃ n : Nat,
    normalizeCode d (encodeExpr (e.rename Fin.val)) = some (e.depth, n) ∧
    CodeCanonical d e.depth n ∧
    WellFormed e.depth (formDecode d e.depth n) ∧
    ∀ ρ : Fin d → PosNat,
      value e.depth (formDecode d e.depth n) (fun i => (ρ i : Nat)) = e.eval ρ

def Target : Prop := LiteralCompilation ∧ RowRepresentation ∧ ExactDepth ∧
  RawDomain ∧ ActualPrimitivePrograms ∧ FullEffectiveNormalization

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizerProgram
