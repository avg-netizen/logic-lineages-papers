module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBodyCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalBodyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalParameterizedBoundedDescentNormalizerSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalSelectionFieldProof OriginalLambdaTraversalFinalSourceProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem transitionAt (p : GlobalSourcePackage.Inputs) (law : FinalTransitionLaw p)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises (finalData p) input typ parameter))) :
    Nonempty (Derivation positive Delta
      ((InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (finalData p)) out input parameter).iff
        (graph2 (canonical p.base p.window) out input parameter))) := by
  obtain ⟨hl⟩ := law positive alpha Delta out input typ parameter
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hl hp⟩

/-- T-fixedness is transported to genuine C-fixedness only at the accepted
parent. The independently proved actual-child C theorem then supplies the
body value; same-final source/type/window pay the reverse T transport. -/
theorem bodyAtType (p : GlobalSourcePackage.Inputs) (law : FinalTransitionLaw p)
    (input d e child typ parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter)))
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter)))
    (ht : Nonempty (Derivation positive Delta (graph1 InternalUnpair.left typ input)))
    (hp : Nonempty (Derivation positive Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (finalData p)) input input parameter))) :
    Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one child bodyParameter ⊓
        (graph1 InternalUnpair.left e child ⊓
          InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
            (InternalOriginalUniformDescentSelection.validity (finalData p)) child child bodyParameter))) := by
  obtain ⟨equation⟩ := transitionAt p law input input typ parameter (andIntro hw (andIntro hs ht))
  obtain ⟨hp0⟩ := hp
  have hC := Derivation.implicationElimination (Derivation.conjunctionLeft equation) hp0
  have hw0 := hw
  rw [finalWindow] at hw0
  have hs0 := hs
  rw [sameValidity] at hs0
  have bodyC := OriginalLambdaTraversalBodyCanonicalProof.bodyFixed p.base p.window
    input d e child parameter bodyParameter hw0 hf hs0 ⟨hC⟩
  have childPremises := finalChildPremises p input d e child parameter bodyParameter hf hw hs
  obtain ⟨childEquation⟩ := transitionAt p law child child e bodyParameter childPremises
  obtain ⟨bodyC0⟩ := bodyC
  have bodyT := Derivation.implicationElimination (Derivation.conjunctionRight childEquation) bodyC0
  have childSource := andRight childPremises
  exact andIntro (andLeft childSource) (andIntro (andRight childSource) ⟨bodyT⟩)

/-- The parent type is bound internally. No body-C, body-T, accessibility,
source calibration or earlier-selected-body theorem is an arithmetic premise. -/
theorem bodyFromParent (p : GlobalSourcePackage.Inputs) (law : FinalTransitionLaw p)
    (input d e child parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter)))
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter)))
    (hp : Nonempty (Derivation positive Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
        (InternalOriginalUniformDescentSelection.validity (finalData p)) input input parameter))) :
    Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one child bodyParameter ⊓
        (graph1 InternalUnpair.left e child ⊓
          InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
            (InternalOriginalUniformDescentSelection.validity (finalData p)) child child bodyParameter))) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Theta typ hj ht
  simp only [conjunctionRename, graph2Rename, graph1Rename, InternalOriginalStepGuard.one,
    sucRelabel, zRelabel, transitionRename]
  simp only [consTermRename, emptyRename] at ht
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph, OriginalVariableRepresentative.windowGraph,
    graph2Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel] at hw'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel] at hs'
  have hp' := renameInto hp j Theta hj
  rw [transitionRename] at hp'
  exact bodyAtType p law (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    typ (parameter.relabel j) (bodyParameter.relabel j) hw' hf' hs' ht hp'

/-- Modular packaging: the only visible supplier is the final transition
law, to be instantiated by its actual proof in the exact final theorem. -/
theorem finalBodyFixed (p : GlobalSourcePackage.Inputs) (law : FinalTransitionLaw p) :
    FinalBodyFixedLaw p := by
  intro positive alpha Delta input d e child parameter bodyParameter
  let P := OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
    (LambdaFields input d e child parameter bodyParameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter ⊓
        InternalParameterizedBoundedDescentNormalizer.transitionGraph (finalData p).oldRepresentative
          (InternalOriginalUniformDescentSelection.validity (finalData p)) input input parameter))
  have hp : Nonempty (Derivation positive (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := bodyFromParent p law input d e child parameter bodyParameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andRight (andRight (andRight hp)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalBodyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalBodyProof
