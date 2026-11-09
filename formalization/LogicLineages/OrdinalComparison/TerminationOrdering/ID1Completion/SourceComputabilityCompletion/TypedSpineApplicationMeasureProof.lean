module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineApplicationMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open SourceComputabilityCompletion.TypedSpine TypedSpineMeasureProof
open SpineApplicationTargets (selectedData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The genuine supplied raw actualJ equation lifts to the original
Object payload measure. The argument contributes no mark premise. The
result mark is an actual original pairing graph, bound by totality later. -/
theorem resultMarked {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (data : Data) (window : Program 1)
    (arrow d e function argument out parameter functionObject outObject functionMark depth resultMark : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) (suc z) function parameter)))
    (ha : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e function argument out parameter)))
    (hf : Nonempty (Derivation body Gamma (marked functionObject functionMark depth)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right function functionObject)))
    (hop : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right out outObject)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing resultMark InternalOriginalStepGuard.one (suc depth)))) :
    Nonempty (Derivation body Gamma (marked outObject resultMark (suc depth))) := by
  have hm := payloadMeasure functionObject function functionMark hfp (andLeft hf)
  have hflag := andLeft (andRight hf)
  have hdepth := andRight (andRight hf)
  obtain ⟨heq⟩ := SpineApplicationProof.applicationEquation data window
    arrow d e function argument out parameter functionMark InternalOriginalStepGuard.one
    depth (suc depth) resultMark
    (andIntro hw (andIntro ha (andIntro hm (andIntro hflag
      (andIntro hdepth (successorValue (Fin.cons depth Fin.elim0)))))))
  obtain ⟨hp'⟩ := hp
  have hout : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph resultMark out)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hp'⟩
  exact andIntro (objectMeasureValue outObject out resultMark hop hout)
    (andIntro (pairLeft resultMark InternalOriginalStepGuard.one (suc depth) hp)
      (pairRight resultMark InternalOriginalStepGuard.one (suc depth) hp))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineApplicationMeasureProof
