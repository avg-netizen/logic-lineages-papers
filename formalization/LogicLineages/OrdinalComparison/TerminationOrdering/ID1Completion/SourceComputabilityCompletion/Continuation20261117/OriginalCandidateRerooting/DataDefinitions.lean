module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.DataDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
structure Data {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (Delta : List (Formula alpha))
    (seed candidate parameter : OTerm alpha) where
  root : OTerm alpha
  left : OTerm alpha
  right : OTerm alpha
  bounds : OTerm alpha
  sourcePair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed root left))
  targetPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate root right))
  sourceBounds : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) bounds left))
  targetBounds : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) bounds right))
  sourceAdmitted : Nonempty (Derivation body Delta
    (graph2 (OriginalClassCodes.admitted n (OriginalConcreteHeadSignature.signature n arity)) (numeral 1) seed parameter))
  targetAdmitted : Nonempty (Derivation body Delta
    (graph2 (OriginalClassCodes.admitted n (OriginalConcreteHeadSignature.signature n arity)) (numeral 1) candidate parameter))

/-- Internal proof utility: every observation of a selector transports. The
final endpoint derives Data rather than requiring it. -/
def Stable (n : Nat) (arity : Fin n → Nat) (P : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter out : OTerm alpha),
  Data n arity body Delta seed candidate parameter →
  Nonempty (Derivation body Delta (graph2 P out seed parameter)) →
  Nonempty (Derivation body Delta (graph2 P out candidate parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.DataDefinitions
