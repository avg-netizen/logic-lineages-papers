module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineSuccessorProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalComputabilityDownwardSyntaxProof InternalRecursionClosureLogicProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open SourceComputabilityFormulaSupportProof
open SourceComputabilityCompletion.TypedSpine GlobalSourceSpineSyntaxProof GlobalSourceSpineStrongProof
open InverseApplicationSyntaxProof (membershipRename)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual source certificate progress below the supplied depth. The
source/comp pair is selected once globally and retained at every witness.
Only the source's original certificate is assumed, not a raw case oracle. -/
theorem certificateLeast (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (base : Data) (oldStep : Program 4) (window : Program 1) (oldVertex oldResult : Program 5)
    (context : Nat) (hw : evaluate window (List.Vector.ofFn ![context]) = 1) (tau : Ty) :
    let src := OuterSelection.source oldSrc oldComp base oldStep window
    let comp := OuterSelection.computability oldComp base window oldVertex oldResult
    ∀ (α : Type) (Gamma : List (Formula α)) (f mark depth g witness : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (InternalStrongInduction.below (atDepth comp context tau (.var (.inr 0))) depth)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (typed comp tau (numeral context) f)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (marked f mark depth)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (certificate src false context f g witness)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (membership false g)) := by
  dsimp only
  intro α Gamma f mark depth g witness hb ht hm hc
  let selected := OuterSelection.data base window
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  have rules := OuterArithmeticProof.arithmeticRules oldSrc oldComp selected
    (RawScalar.checker selected) oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure
    window oldVertex oldResult context hw
  have htypedG := closedApply (rules.typedDown α tau f g)
    (andIntro ht (edgeIntroduction hc))
  apply GlobalSourceSpineQueriesProof.coordinateCases BottomSpineMeasure.measure (numeral context) f g _
  intro β j Delta gammaCode fp gp parameter targetMark targetDepth hj hgamma hfp hgp hp hmark hdepth
  rw [membershipRename]
  have hb' := renameInto hb j Delta hj
  rw [belowDepthRename] at hb'
  have hm' := renameInto hm j Delta hj
  rw [markedRename] at hm'
  have hc' := renameInto hc j Delta hj
  rw [certificateRename] at hc'
  have ht' := renameInto htypedG j Delta hj
  simp only [typedRename,GuardedSourceSyntaxProof.numeralRename] at ht'
  simp only [GuardedSourceSyntaxProof.numeralRename] at hp
  have hwindow := GuardedSourceCertificateProof.windowNumeral
    (body := SourcePresentation.sourceBody src context) (Gamma := Delta) (α := β) window context hw
  have hraw := OuterPositiveRawProof.rawPositiveRecover oldSrc oldComp selected
    (RawScalar.checker selected) oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window
    context (f.relabel j) (g.relabel j) (witness.relabel j) gammaCode fp gp parameter
    hwindow hgamma hfp hgp hp hc'
  have hdecrease := GlobalSourceSpineMeasureProof.guardedProgress (edgeChecker selected oldStep)
    (f.relabel j) (g.relabel j) (witness.relabel j) parameter fp gp
    (mark.relabel j) targetMark (depth.relabel j) targetDepth hm' hfp hgp hmark hdepth hraw
  exact GlobalSourceSpineInductionProof.belowApply comp context tau
    (depth.relabel j) targetDepth (g.relabel j) targetMark hb'
    (andRight hdecrease) ht' (andLeft hdecrease)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineSuccessorProof
