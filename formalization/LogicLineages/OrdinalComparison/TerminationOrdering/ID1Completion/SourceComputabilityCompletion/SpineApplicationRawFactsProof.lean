module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalParameterizedCanonicalResultFoldConsumerProof InternalParameterizedCanonicalResultFoldOpeningProof
open InternalOriginalUniformApplicationTypingApplicationProof
open InternalTagArithmeticSyntaxProof (OTerm)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Keep the raw arithmetic facts opaque at an ARBITRARY Data parameter.
Concrete source normalization is instantiated only after this derivation,
so proof elaboration does not repeatedly expand its oldR/V/member Programs. -/
def rawFactsFormula (data : Data) (arrow d e f b raw out parameter : OTerm α) : Formula α :=
  graph2 (InternalOriginalUniformDescentSelection.validity data)
      InternalOriginalStepGuard.one raw parameter ⊓
    (graph2 InternalListCodec.consCode arrow d e ⊓
      (graph1 InternalUnpair.left arrow f ⊓
        (graph1 InternalUnpair.left d b ⊓
          graph2 (InternalOriginalUniformDescentSelection.representative data) out raw parameter)))

theorem rawFacts (data : Data) (arrow d e f a out parameter b raw : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises data arrow d e f a out parameter)))
    (hn : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph data b a parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f b))) :
    Nonempty (Derivation body Gamma (rawFactsFormula data arrow d e f b raw out parameter)) := by
  have har := andLeft h
  have hm := andLeft (andRight h)
  have hf := andLeft (andRight (andRight h))
  have ha := andLeft (andRight (andRight (andRight h)))
  have hj := andRight (andRight (andRight (andRight h)))
  have hff := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data) data.member f arrow parameter hf
  have haf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data) data.member a d parameter ha
  have hb := andRight (certifiedAt data b a d parameter
    (andLeft (andRight haf)) (andLeft (andRight (andRight haf))) hn)
  have hv := rawValidity data arrow d e f b raw parameter har
    (andLeft (andRight (andRight hff))) (andLeft (andRight hb)) hm
    (andLeft (andRight hff)) (andLeft hb) hr
  have hout := combineRecover data d e f b raw out parameter hr
    (applicationCombine data d e f a out parameter b hn hj)
  exact andIntro hv (andIntro har (andIntro (andLeft (andRight (andRight hff)))
    (andIntro (andLeft (andRight hb)) hout)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
