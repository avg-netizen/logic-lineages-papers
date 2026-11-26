module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIterationIffProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalParameterizedBoundedDescentNormalizerSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open OriginalIndexedObserverIteration
open OriginalIndexedObserverDefinitions (ActualRange)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the ACTUAL bounded iteration from the original fallback graph.
Validity must be derived independently from the caller's real condition. -/
theorem selectedIff (R V C : Program 2) (O : Program 3)
    (closure : Closure ⟨InternalParameterizedBoundedDescentNormalizer.transition R V,C,O⟩)
    (supply : Preservation ⟨InternalParameterizedBoundedDescentNormalizer.transition R V,C,O⟩)
    (out input parameter mark cutoff : InternalGraphComposition.OTerm alpha)
    (hRange : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 C InternalOriginalStepGuard.one input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 V InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.fallbackRepresentative R V) out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph3 O mark cutoff out parameter).iff (graph3 O mark cutoff input parameter))) := by
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover R V out input parameter hr hv
  have hrepeat := normalizerRecover R V out input parameter hn
  exact OriginalIndexedObserverIterationIffProof.repeatIff
    ⟨InternalParameterizedBoundedDescentNormalizer.transition R V,C,O⟩ closure supply
    out (suc input) input parameter mark cutoff hRange ha hrepeat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSelectedProof
