module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationBuilderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldConsumerProof InternalParameterizedCanonicalResultFoldOpeningProof
open InternalOriginalUniformApplicationTypingApplicationProof
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SpineApplicationTargets (selectedData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atArgument (data : Data) (window : Program 1)
    (arrow d e f a out parameter fm flag depth next mark b : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises data window arrow d e f a out parameter fm flag depth next)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) b a parameter))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark out).iff (graph2 InternalPairing.pairing mark flag next))) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons b Fin.elim0)))) _
  intro β j Delta raw hj hr
  rw [SpineApplicationRawProof.equationRename]
  have h' := renameInto h j Delta hj
  rw [premisesRename] at h'
  have hn' := renameInto hn j Delta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hn'
  simp only [consTermRename,emptyRename] at hr
  exact atRaw data window (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j)
    (a.relabel j) (out.relabel j) (parameter.relabel j) (fm.relabel j)
    (flag.relabel j) (depth.relabel j) (next.relabel j) (mark.relabel j) (b.relabel j) raw h' hn' hr


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
