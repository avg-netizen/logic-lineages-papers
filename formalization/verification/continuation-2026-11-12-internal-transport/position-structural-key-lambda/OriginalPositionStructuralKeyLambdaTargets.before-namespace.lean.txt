module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion

open OriginalPositionStructuralKeyOpeningDefinitions
open InternalTagArithmeticSyntaxProof (suc)
/-- Local original lambda constructor interface. The shared child observation
is at the successor cutoff and the actual common child parameter. No erased
context, transformed source validity, or key covariance is assumed. This is
not a full-fold theorem: a traversal consumer must supply these original
source and constructor graphs. -/
def ActualLambda : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input out domain codomain child childOut parameter childParameter cutoff childMark mark : OTerm alpha),
 let O := OriginalClassContextAllPositionObserver.positionObservation
   (OriginalStructuralClassKeyDefinitions.key p H G W)
 Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)) →
 Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) child childParameter)) →
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) childOut childParameter)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter)) →
 Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields out domain codomain childOut parameter childParameter)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input domain codomain child)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out domain codomain childOut)) →
 Nonempty (Derivation body Delta (graph3 O childMark (suc cutoff) child childParameter)) →
 Nonempty (Derivation body Delta (graph3 O childMark (suc cutoff) childOut childParameter)) →
 Nonempty (Derivation body Delta
   ((graph3 O mark cutoff out parameter).iff (graph3 O mark cutoff input parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaTargets
