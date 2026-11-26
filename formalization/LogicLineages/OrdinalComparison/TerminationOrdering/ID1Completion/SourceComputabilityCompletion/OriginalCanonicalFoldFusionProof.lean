module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion OriginalCanonicalFoldFusionSyntaxProof
open OriginalCanonicalFoldFusionBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The final right-payload witness is bound and eliminated inside the calculus. -/
theorem invariantAtInput (data : Data) (window : Program 1) (source target : Program 2)
    (closed : ClosedLaw data window source target) (app : ApplicationLaw data window source target)
    (out input typ parameter : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [outputInvariantRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  exact atPayloadApply data window source target payload (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j)
    (OriginalCanonicalFoldFusionInductionProof.payloadInvariant data window source target closed app payload) hr hp'

/-- Program totality and functionality upgrade the internally derived
forward comparison to the full arbitrary-output equivalence. -/
theorem iffAtInput (data : Data) (window : Program 1) (source target : Program 2)
    (closed : ClosedLaw data window source target) (app : ApplicationLaw data window source target)
    (out input typ parameter : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window input parameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises data input typ parameter))) :
    Nonempty (Derivation body Gamma
      ((graph2 source out input parameter).iff (graph2 target out input parameter))) := by
  apply programCases source (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta value hj hv
  rw [OriginalApplicationSidecarTransitionGraphProof.binaryIffRename]
  simp only [consTermRename,emptyRename] at hv
  have hp' := renameInto hp j Delta hj
  simp only [conjunctionRename,OriginalFunctionNeutrality.windowGraph,
    OriginalVariableRepresentative.windowGraph,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename] at hp'
  have htarget := invariantAtInput data window source target closed app value
    (input.relabel j) (typ.relabel j) (parameter.relabel j)
    (andIntro (andLeft hp') (andIntro (andRight hp') hv))
  exact OriginalApplicationSidecarTransitionGraphProof.commonOutputIff source target value
    (out.relabel j) (input.relabel j) (parameter.relabel j) hv htarget

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionProof
