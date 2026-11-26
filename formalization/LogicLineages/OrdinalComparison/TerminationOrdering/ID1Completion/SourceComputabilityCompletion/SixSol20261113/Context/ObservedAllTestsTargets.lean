module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertion OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ObservedAllTestsDefinitions
/-- Introduction for the literal original finite conjunction scan. No
external pointwise family or metalevel numeral bound replaces its premise. -/
def ActualScan : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (count seed candidate parameter : OTerm alpha),
 Nonempty (Derivation body Delta (BoundedTests R count seed candidate parameter)) →
 Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed candidate parameter))
/-- Introduction for the unchanged all-position observer. Actual parameter
right projection and actual context length connect the quantified bound to
its literal scan. This generic supplier makes no final-tuple or semantic claim. -/
def ActualAllTests : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (seed candidate parameter gamma count : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)) →
 Nonempty (Derivation body Delta (lengthGraph count gamma)) →
 Nonempty (Derivation body Delta (BoundedTests R count seed candidate parameter)) →
 Nonempty (Derivation body Delta (graph3 (allTests R) (suc z) seed candidate parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsTargets
