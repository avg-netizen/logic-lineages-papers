module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawFactsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawProof
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

theorem atRaw (data : Data) (window : Program 1)
    (arrow d e f a out parameter fm flag depth next mark b raw : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises data window arrow d e f a out parameter fm flag depth next)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) b a parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f b))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark out).iff (graph2 InternalPairing.pairing mark flag next))) := by
  have hw := andLeft h
  have happ := andLeft (andRight h)
  have hfm := andLeft (andRight (andRight h))
  have hl := andLeft (andRight (andRight (andRight h)))
  have hdepth := andLeft (andRight (andRight (andRight (andRight h))))
  have hnext := andRight (andRight (andRight (andRight (andRight h))))
  have hfacts := rawFacts (selectedData data window) arrow d e f a out parameter b raw happ hn hr
  have hv := andLeft hfacts
  have har := andLeft (andRight hfacts)
  have hfl := andLeft (andRight (andRight hfacts))
  have hbl := andLeft (andRight (andRight (andRight hfacts)))
  have hout := andRight (andRight (andRight (andRight hfacts)))
  have hwraw := BottomDescentStepProof.windowChange window (suc z) f raw parameter hw
  have hi := SpineApplicationSelectedProof.selectedIff data window out raw parameter mark
    (activeValue data window raw parameter hwraw hv) hout
  have hraw := SpineApplicationRawProof.rawEquation arrow d e f b raw fm flag depth next mark
    har hfl hbl hr hfm hl hdepth hnext
  exact chainIff _ _ _ hi hraw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
