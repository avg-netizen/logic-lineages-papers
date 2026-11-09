module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationArgumentProof
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

theorem applicationEquation (data : Data) (window : Program 1)
    (arrow d e f a out parameter fm flag depth next mark : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises data window arrow d e f a out parameter fm flag depth next))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark out).iff (graph2 InternalPairing.pairing mark flag next))) := by
  apply programCases (InternalParameterizedCanonicalResultFold.foldN (selectedData data window))
    (Fin.cons a (Fin.cons parameter Fin.elim0)) _
  intro β j Delta b hj hn
  rw [SpineApplicationRawProof.equationRename]
  have h' := renameInto h j Delta hj
  rw [premisesRename] at h'
  simp only [consTermRename,emptyRename] at hn
  exact atArgument data window (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j)
    (a.relabel j) (out.relabel j) (parameter.relabel j) (fm.relabel j)
    (flag.relabel j) (depth.relabel j) (next.relabel j) (mark.relabel j) b h' hn

theorem actualParameterizedApplicationSpineEquation : SpineApplicationTargets.ActualParameterizedApplicationSpineEquation := by
  intro body data window α Delta arrow d e f a out parameter fm flag depth next mark
  let H := premises data window arrow d e f a out parameter fm flag depth next
  obtain ⟨d⟩ := applicationEquation (body := body) (Gamma := H :: Delta)
    data window arrow d e f a out parameter fm flag depth next mark
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
