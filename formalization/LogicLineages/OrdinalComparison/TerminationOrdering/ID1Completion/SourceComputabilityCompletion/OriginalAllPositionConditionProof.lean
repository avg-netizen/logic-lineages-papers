module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoderTransportLogicalProof (iffForward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Only representative selection changes; the original source/window and
membership code survive literally, not merely under native calibration. -/
theorem minimumSource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    (OriginalRankGuardedRepresentative.transparentInputs H G W
      (OriginalClassContextAllPositionSelection.inputs p H G W P)).base.oldSource =
      OriginalUniverseDecoder.source H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W := rfl

theorem minimumWindow (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    (OriginalRankGuardedLeaf.refined (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).window = p.window := rfl

theorem conditionDomain (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition
        (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W) (suc z) input parameter))) :
    Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W input parameter)) := by
  have hf := OriginalRankGuardedLeafTupleProof.conditionFactors
    (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W input parameter ha
  have hs := iffForward (OriginalRankGuardedLeafTupleProof.priorSourceIff
    (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W (suc z) input parameter) (andRight hf)
  rw [minimumSource] at hs
  have hw := andLeft hf
  rw [minimumWindow] at hw
  have ht := OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget H G
    (InternalOriginalUniformContextMembership.contextMember p.base.member) W input parameter hs
  have hactivation : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) input parameter)) :=
    conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hs
  exact andIntro ht hactivation

theorem conditionDomainProgram (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition
        (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W) (suc z) input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalActiveClassKernel.domainProgram p H G W) (suc z) input parameter)) := by
  have h := conditionDomain p H G W P input parameter ha
  exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft h) (andRight h)

/-- Actual prior bounded-descent transition, before the selected OTHER sidecar. -/
def priorIteration (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (observer : Program 3) : OriginalIndexedObserverIteration.Data where
  transition := OriginalGuardedObserverIteration.step
    (OriginalRankGuardedLeafPriorProof.iterationData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)
  condition := OriginalRankGuardedLeafTupleProof.condition (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W
  observer := observer

theorem priorClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (observer : Program 3) : OriginalIndexedObserverIteration.Closure (priorIteration p H G W P observer) := by
  intro body alpha Delta out input parameter ha ht
  exact OriginalRankGuardedLeafPriorProof.iterationClosure
    (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W body alpha Delta out input parameter ha ht

/-- Proof-side indexed data for the EXISTING actual bounded-descent step.
The stronger OTHER condition is the checked invariant of that step. -/
def actualIteration (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (observer : Program 3) : OriginalIndexedObserverIteration.Data where
  transition := OriginalGuardedObserverIteration.step
    (OriginalRankGuardedLeafProof.iterationData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W)
  condition := OriginalRankGuardedLeafProof.condition (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W
  observer := observer

theorem actualClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (observer : Program 3) : OriginalIndexedObserverIteration.Closure (actualIteration p H G W P observer) := by
  intro body alpha Delta out input parameter ha ht
  exact OriginalRankGuardedLeafProof.iterationClosure
    (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W body alpha Delta out input parameter ha ht

theorem actualConditionDomain (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (observer : Program 3) (input parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (OriginalIndexedObserverIteration.activeGraph (actualIteration p H G W P observer) input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalActiveClassKernel.domainProgram p H G W) (suc z) input parameter)) := by
  have h := conjunctionRecover (OriginalRankGuardedLeafTupleProof.condition
    (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W) OriginalRankGuardedLeafProof.otherAt
    (Fin.cons input (Fin.cons parameter Fin.elim0)) ha
  exact conditionDomainProgram p H G W P input parameter (andLeft h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
