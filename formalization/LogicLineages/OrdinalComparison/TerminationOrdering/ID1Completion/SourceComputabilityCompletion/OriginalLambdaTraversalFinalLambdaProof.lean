module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalParameterizedCanonicalResultFoldSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalFinalSourceProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem composeIff (A B C : Formula alpha)
    (hab : Nonempty (Derivation positive Delta (A.iff B)))
    (hbc : Nonempty (Derivation positive Delta (B.iff C))) :
    Nonempty (Derivation positive Delta (A.iff C)) := by
  obtain ⟨habA⟩ := withHyp hab A
  obtain ⟨hbcA⟩ := withHyp hbc A
  have forward : Derivation positive (A :: Delta) C :=
    Derivation.implicationElimination (Derivation.conjunctionLeft hbcA)
      (Derivation.implicationElimination (Derivation.conjunctionLeft habA)
        (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨habC⟩ := withHyp hab C
  obtain ⟨hbcC⟩ := withHyp hbc C
  have backward : Derivation positive (C :: Delta) A :=
    Derivation.implicationElimination (Derivation.conjunctionRight habC)
      (Derivation.implicationElimination (Derivation.conjunctionRight hbcC)
        (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem canonicalAt (p : GlobalSourcePackage.Inputs) (law : FinalCanonicalLaw p)
    (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises (finalData p) input typ parameter))) :
    Nonempty (Derivation positive Delta
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p) out input parameter).iff
        (graph2 (canonical p.base p.window) out input parameter))) := by
  obtain ⟨hl⟩ := law positive alpha Delta out input typ parameter
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hl hp⟩

/-- The actual final child fold is transported to the SAME C only after
its source/type/window have been derived internally at the actual extended
parameter. The parent's literal lambda recurrence then has no supplied body
fixedness or earlier fold premise. -/
theorem lambdaAtType (p : GlobalSourcePackage.Inputs) (law : FinalCanonicalLaw p)
    (input d e child childOut out typ parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter)))
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter)))
    (ht : Nonempty (Derivation positive Delta (graph1 InternalUnpair.left typ input)))
    (hc : Nonempty (Derivation positive Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (finalData p) childOut child bodyParameter))) :
    Nonempty (Derivation positive Delta
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p) out input parameter).iff
        (graph3 OriginalLambdaConstructor.constructor out d e childOut))) := by
  have hp := andIntro hw (andIntro hs ht)
  have childPremises := finalChildPremises p input d e child parameter bodyParameter hf hw hs
  obtain ⟨childEquation⟩ := canonicalAt p law childOut child e bodyParameter childPremises
  obtain ⟨hc0⟩ := hc
  have childC := Derivation.implicationElimination (Derivation.conjunctionLeft childEquation) hc0
  obtain ⟨recurrence⟩ := OriginalLambdaTraversalInternalLambdaProof.actualOriginalLambdaTraversalInternalLambda
    positive (leaf p.base p.window) alpha Delta input d e child childOut out parameter bodyParameter
  obtain ⟨argument⟩ := andIntro hf ⟨childC⟩
  exact composeIff _ _ _ (canonicalAt p law out input typ parameter hp)
    ⟨Derivation.implicationElimination recurrence argument⟩

/-- Original graph totality binds the parent type, leaving every frozen
arithmetic premise and both directions of the constructor equation intact. -/
theorem lambdaFromParent (p : GlobalSourcePackage.Inputs) (law : FinalCanonicalLaw p)
    (input d e child childOut out parameter bodyParameter : OTerm alpha)
    (hw : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter)))
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter)))
    (hc : Nonempty (Derivation positive Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (finalData p) childOut child bodyParameter))) :
    Nonempty (Derivation positive Delta
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p) out input parameter).iff
        (graph3 OriginalLambdaConstructor.constructor out d e childOut))) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Theta typ hj ht
  change Nonempty (Derivation positive Theta
    (((InternalParameterizedCanonicalResultFold.foldGraph (finalData p) out input parameter).relabel j).iff
      ((graph3 OriginalLambdaConstructor.constructor out d e childOut).relabel j)))
  rw [foldGraphRename, graph3Rename]
  simp only [consTermRename, emptyRename] at ht
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph, OriginalVariableRepresentative.windowGraph,
    graph2Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel] at hw'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel] at hs'
  have hc' := renameInto hc j Theta hj
  rw [foldGraphRename] at hc'
  exact lambdaAtType p law (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (childOut.relabel j) (out.relabel j) typ (parameter.relabel j) (bodyParameter.relabel j)
    hw' hf' hs' ht hc'

/-- Conditional packaging only; the exact final target instantiates the
proved canonical law rather than adding it as an arithmetic premise. -/
theorem finalLambdaEquation (p : GlobalSourcePackage.Inputs) (law : FinalCanonicalLaw p) :
    FinalLambdaEquation p := by
  intro positive alpha Delta input d e child childOut out parameter bodyParameter
  let P := OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter ⊓
    (LambdaFields input d e child parameter bodyParameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph (finalData p) childOut child bodyParameter))
  have hp : Nonempty (Derivation positive (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := lambdaFromParent p law input d e child childOut out parameter bodyParameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andRight (andRight (andRight hp)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalLambdaProof
