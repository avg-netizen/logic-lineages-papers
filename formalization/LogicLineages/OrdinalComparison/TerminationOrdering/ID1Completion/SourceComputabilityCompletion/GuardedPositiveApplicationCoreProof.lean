module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open SpineApplicationTargets (selectedData parameters)
open UniformCertificateCompletion
open GuardedPositiveApplicationQueriesProof (facts)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem outputMark (data : Data) (window : Program 1)
    (arrow d e f a out parameter mark flag depth nextMark : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) (suc z) f parameter)))
    (ha : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e f a out parameter)))
    (hm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph mark f)))
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag mark)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth mark)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing nextMark flag (suc depth)))) :
    Nonempty (Derivation body Gamma (BottomSpineMeasure.graph nextMark out)) := by
  obtain ⟨he⟩ := SpineApplicationProof.applicationEquation data window arrow d e f a out parameter
    mark flag depth (suc depth) nextMark
    (andIntro hw (andIntro ha (andIntro hm (andIntro hf (andIntro hd
      (successorValue (Fin.cons depth Fin.elim0)))))))
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight he) hp⟩

/-- Literal bottom rejection is obtained from its independent checked
application theorem, rather than inferred from the native mark calibration. -/
theorem outputNonBottom (data : Data) (window : Program 1)
    (arrow d e f a out parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) (suc z) f parameter)))
    (ha : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e f a out parameter))) :
    Nonempty (Derivation body Gamma
      (graph1 BottomRepresentative.bottomTest (suc z) out).not) := by
  rw [SpineApplicationProof.selectedDataEq] at ha
  exact BottomApplicationProof.applicationNonBottom (parameters data window) window
    arrow d e f a out parameter hw ha

theorem atValues (data : Data) (window : Program 1) (oldStep : Program 4)
    (arrow d e f g a out other certificate mapped parameter : OTerm α) (ys : Fin 8 → OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) (suc z) f parameter)))
    (hf : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e f a out parameter)))
    (hg : Nonempty (Derivation body Gamma
      (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e g a other parameter)))
    (hi : Nonempty (Derivation body Gamma
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker (selectedData data window) oldStep) f g certificate parameter)))
    (hmapped : Nonempty (Derivation body Gamma
      (InternalParameterizedPathChecker.positiveGraph (edgeChecker (selectedData data window) oldStep)
        out other mapped parameter)))
    (hq : Nonempty (Derivation body Gamma (facts BottomSpineMeasure.measure f g ys))) :
    Nonempty (Derivation body Gamma
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        (edgeChecker (selectedData data window) oldStep) out other mapped parameter)) := by
  have hm0 := andLeft hq
  have q1 := andRight hq
  have hm1 := andLeft q1
  have q2 := andRight q1
  have hfl0 := andLeft q2
  have q3 := andRight q2
  have hdp0 := andLeft q3
  have q4 := andRight q3
  have hfl1 := andLeft q4
  have q5 := andRight q4
  have hdp1 := andLeft q5
  have q6 := andRight q5
  have hp0 := andLeft q6
  have hp1 := andRight q6
  have hwg := BottomDescentStepProof.windowChange window (suc z) f g parameter hw
  have hout := outputMark data window arrow d e f a out parameter
    (ys 0) (ys 2) (ys 3) (ys 6) hw hf hm0 hfl0 hdp0 hp0
  have hother := outputMark data window arrow d e g a other parameter
    (ys 1) (ys 4) (ys 5) (ys 7) hwg hg hm1 hfl1 hdp1 hp1
  have hinputMarked := andIntro hm0 (andIntro hm1 (andIntro hdp0 hdp1))
  have hc := PositiveSpineRulesProof.recover BottomRepresentative.bottomTest BottomSpineMeasure.measure
    (edgeChecker (selectedData data window) oldStep) f g certificate parameter
    (ys 0) (ys 1) (ys 3) (ys 5) hinputMarked hi
  have hconditional := GuardedPositiveApplicationArithmeticProof.conditionalSucc
    (ys 0) (ys 1) (ys 6) (ys 7) (ys 2) (ys 4) (ys 3) (ys 5)
    hfl0 hfl1 hp0 hp1 (andRight (andRight hc))
  have hn := outputNonBottom data window arrow d e f a out parameter hw hf
  have houtputMarked := andIntro hout (andIntro hother
    (andIntro (pairRight (ys 6) (ys 2) (suc (ys 3)) hp0)
      (pairRight (ys 7) (ys 4) (suc (ys 5)) hp1)))
  exact PositiveSpineRulesProof.value BottomRepresentative.bottomTest BottomSpineMeasure.measure
    (edgeChecker (selectedData data window) oldStep) out other mapped parameter
    (ys 6) (ys 7) (suc (ys 3)) (suc (ys 5)) houtputMarked
    (andIntro hmapped (andIntro hn hconditional))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GuardedPositiveApplicationCoreProof
