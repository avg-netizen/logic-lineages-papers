module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationOtherProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The OTHER branch needs no retained-R compatibility assumption. -/
theorem atOther (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input out parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input))) :
 Nonempty (Derivation body Delta (Domain p H G W out parameter ⊓ Same p H G W input out parameter)) := by
 let leaf := OriginalLambdaTraversalSelection.leaf (refined p H G W P).base (refined p H G W P).window
 obtain ⟨law⟩ := OriginalLambdaTraversalInternalLeafProof.actualOriginalLambdaTraversalInternalLeaf body leaf alpha Delta input out parameter
 obtain ⟨tag⟩ := ht
 obtain ⟨comp⟩ := hc
 have hl : Nonempty (Derivation body Delta (graph2 leaf out input parameter)) :=
  ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination law tag)) comp⟩
 exact SixSol20261113.Erasure.EvaluatorOtherPreservationProof.actualOtherPreservation
  p H G W P body alpha Delta input out parameter hd ⟨tag⟩ hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationOtherProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationOtherProof
