module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Targets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

def InternalFilter : Prop := ∀ (H : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw out needle symbols types value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (filterCandidates H) out raw symbols)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) ↔
   Nonempty (Derivation body Delta (qualifies raw needle value)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.Targets
