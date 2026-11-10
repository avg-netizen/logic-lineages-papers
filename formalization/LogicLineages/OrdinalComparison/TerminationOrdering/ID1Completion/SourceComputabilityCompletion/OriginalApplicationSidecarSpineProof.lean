module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarSpine OriginalApplicationSidecarSpineSyntaxProof
open OriginalApplicationSidecarSpineBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The final right-payload witness is bound and eliminated inside the calculus. -/
theorem spineAtInput (data : Data) (window : Program 1) (out input typ parameter value : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [conclusionRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  exact atPayloadApply data window payload (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) (value.relabel j)
    (OriginalApplicationSidecarSpineInductionProof.payloadSpine data window payload) hr hp'

theorem actualOriginalApplicationSidecarSpine :
    OriginalApplicationSidecarSpineTargets.ActualOriginalApplicationSidecarSpine := by
  intro body data window α Delta out input typ parameter value
  obtain ⟨h⟩ := spineAtInput (body := body)
    (Gamma := premises data window out input typ parameter :: Delta)
    data window out input typ parameter value ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineProof.actualOriginalApplicationSidecarSpine
