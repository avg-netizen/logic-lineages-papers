module

public import LogicLineages.ComputabilityKnowledge.WWFiniteEnvelope
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.WWFiniteEnvelope

open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration
open LogicLineages.ComputabilityKnowledge.WWFiniteEnvelope

def LiteralNarrowing : Prop :=
  ∀ (d : Nat) (e : Expr Nat) (h : Bounded d e), (narrow d e h).rename Fin.val = e

def LiteralEnvelope : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)),
    (envelope d e).rename Fin.val = FiniteDepthEnvelope.envelope (e.rename Fin.val) ∧
      (envelope d e).depth = 0

def SharedPositiveControl : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)), e.depth ≤ 2 → ∀ ρ : Fin d → PosNat,
    0 < (envelope d e).eval ρ ∧
      e.eval ρ ≤ LogicLineages.OrdinalComparison.fastControl 2 ((envelope d e).eval ρ)

def ActualEncodedConstruction : Prop :=
  Computable (fun p : Nat × List Nat => FiniteDepthEnvelope.envelopeCode p.1 p.2) ∧
  (∀ (d : Nat) (e : Expr (Fin d)),
    FiniteDepthEnvelope.envelopeCode d (encodeExpr (e.rename Fin.val)) =
      some (encodeExpr ((envelope d e).rename Fin.val))) ∧
  (∀ (d : Nat) (raw : List Nat),
    FiniteDepthEnvelope.envelopeCode d raw = none ↔ decodeExpr d raw = none)

def Target : Prop := LiteralNarrowing ∧ LiteralEnvelope ∧ SharedPositiveControl ∧ ActualEncodedConstruction

end LogicLineages.ComputabilityKnowledge.Comparators.WWFiniteEnvelope
