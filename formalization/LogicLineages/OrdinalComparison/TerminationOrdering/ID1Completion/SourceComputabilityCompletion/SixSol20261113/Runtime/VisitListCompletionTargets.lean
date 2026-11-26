module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ActualEmpty : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)),
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R (numeral 0) (numeral 0)))
/-- Exact operational cons composition, with the genuine head and tail
completion suppliers explicit. Counts and produced rows are constructed. -/
def ActualCons : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (size job frame tailTagged tagged : OTerm alpha),
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) →
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R size tailTagged)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) job)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)) →
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R (suc size) tagged))
/-- Internal induction on the actual symbolic length. This is not a native
list induction and does not supply the recursive job-admission theorem. -/
def ActualFiniteVisits : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (size jobs tagged : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)) →
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)) →
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R size tagged))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionTargets
