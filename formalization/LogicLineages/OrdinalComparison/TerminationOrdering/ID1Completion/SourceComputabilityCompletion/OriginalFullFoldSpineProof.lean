module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine OriginalFullFoldSpineSyntaxProof OriginalFullFoldSpineBindingProof
open OriginalFullFoldSpineTargets
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (emptyRename)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original right-payload witness is eliminated internally after the
closed strong induction. The output and observer remain the supplied terms. -/
theorem spineAtInput (base : Data) (window : Program 1)
    (out input typ parameter mark : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Gamma
      (premises (SpineApplicationTargets.selectedData base window) window out input typ parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro beta j Delta payload hinc hr
  rw [conclusionRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Delta hinc
  rw [premisesRename] at hp'
  exact atPayloadApply (SpineApplicationTargets.selectedData base window) window
    payload (input.relabel j) (typ.relabel j) (out.relabel j) (parameter.relabel j) (mark.relabel j)
    (OriginalFullFoldSpineInductionProof.payloadSpine base window payload) hr hp'

theorem actualOriginalFullFoldSpinePreservation :
    ActualOriginalFullFoldSpinePreservation := by
  intro base window body alpha Gamma out input typ parameter mark
  obtain ⟨h⟩ := spineAtInput (body := body)
    (Gamma := premises (SpineApplicationTargets.selectedData base window)
      window out input typ parameter :: Gamma)
    base window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalFinalFullFoldSpinePreservation :
    ActualOriginalFinalFullFoldSpinePreservation := by
  intro p
  let r := OriginalApplicationSidecar.finalInputs p
  change FullFoldMarkPreservation (SpineApplicationTargets.selectedData r.base r.window) r.window
  exact actualOriginalFullFoldSpinePreservation r.base r.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof.actualOriginalFullFoldSpinePreservation
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineProof.actualOriginalFinalFullFoldSpinePreservation
