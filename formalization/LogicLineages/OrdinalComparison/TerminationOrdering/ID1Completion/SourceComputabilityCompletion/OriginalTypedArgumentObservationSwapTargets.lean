module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationSwapDefinitions
/-- Actual graph-level typed adjacent swap implies acceptance of its literal
numeric observation exchange certificate. R and parameter are unchanged.
No native semantics, source validity or arbitrary permutation premise. -/
def ActualSwap : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate : OTerm alpha),
 Nonempty (Derivation body []
 ((Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw ⊓
  (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter ⊓
  (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter ⊓
   Certificate typedQ typedR observedTail rest payload certificate))).imp
  (graph3 OriginalNumericListSortExchange.edge (numeral 1) source target certificate)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapTargets
