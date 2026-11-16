module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedDecoderInternalAcceptance
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual decoder mode plus actual original bounds/depth observations only.
No raw-code validity, calibrated H, native image or semantic measure premise. -/
def InternalTermDepthBound : Prop := ∀ (n : Nat) (H : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (typ raw gamma pair size label depth : OTerm alpha),
  Nonempty (Derivation body Delta (TermAccepted H typ raw gamma)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)) →
  Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)) →
  Nonempty (Derivation body Delta (termBound depth size))

/-- Actual decoder mode plus actual original bounds/depth observations only.
No raw-code validity, calibrated H, native image or semantic measure premise. -/
def InternalArgumentsDepthBound : Prop := ∀ (n : Nat) (H : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (typ raw gamma pair size label depth : OTerm alpha),
  Nonempty (Derivation body Delta (ArgumentsAccepted H typ raw gamma)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)) →
  Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)) →
  Nonempty (Derivation body Delta (argumentsBound depth size))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.Targets
