module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (existsOne)
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open CodedDeletionTraceDefinitions SixSol20261113.Erasure.EvaluatorErasureDefinitions
/-- Genuine arithmetic-count uniform preservation for a literal coded trace.
Only initial source/evaluator agreement is assumed. Actual list length and
endpoint lookups retain real trace geometry; no Object/canonicality claim. -/
def ActualCodedChain : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (trace steps c left right parameter gamma finalLeft finalRight finalParameter finalGamma : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc steps) trace)) →
 Nonempty (Derivation body Delta (StateAt trace z left right parameter gamma)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (AllSteps trace steps c)) →
 Nonempty (Derivation body Delta (StateAt trace steps finalLeft finalRight finalParameter finalGamma)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W finalLeft finalRight finalParameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTargets
