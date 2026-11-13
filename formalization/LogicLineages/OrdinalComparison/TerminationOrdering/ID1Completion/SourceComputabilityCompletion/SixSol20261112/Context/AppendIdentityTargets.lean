module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
/-- The original actual append has its literal right identity at every code. -/
def ActualRightZero : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (front : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append front front z))
/-- Equality of actual append outputs with the SAME prefix recovers equality
of the original suffixes. No native decoding, length bound or cancellation law
is supplied as a premise. -/
def ActualLeftCancellation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (front left right joined : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append joined front left)) →
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append joined front right)) →
  Nonempty (Derivation body Delta (eqn left right))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityTargets
