module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatCommutationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker
open InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalParameterizedApplicationStepCheckerRepeatSupportProof
open InternalParameterizedApplicationStepCheckerRepeatCommutationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalListCodec InternalListCodecSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem frontConsForward (transition : Program 2)
    (code head tail out initial next parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 consCode code head tail)))
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out code initial parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out tail next parameter)) := by
  apply programCases (repeatP transition) (Fin.cons tail (Fin.cons initial (Fin.cons parameter Fin.elim0))) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Delta hj
  rw [graph2Rename] at hc'
  have hn' := renameInto hn j Delta hj
  rw [graph2Rename] at hn'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have ht := repeatConsRecover transition (code.relabel j) (head.relabel j) (tail.relabel j)
    result (out.relabel j) (initial.relabel j) (parameter.relabel j) hc' hr ho'
  exact commuteValue transition (tail.relabel j) (initial.relabel j) (next.relabel j)
    result (out.relabel j) (parameter.relabel j) hn' hr ht

theorem frontConsBackward (transition : Program 2)
    (code head tail out initial next parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 consCode code head tail)))
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out tail next parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code initial parameter)) := by
  apply programCases (repeatP transition) (Fin.cons code (Fin.cons initial (Fin.cons parameter Fin.elim0))) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Delta hj
  rw [graph2Rename] at hc'
  have hn' := renameInto hn j Delta hj
  rw [graph2Rename] at hn'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have ht := frontConsForward transition (code.relabel j) (head.relabel j) (tail.relabel j)
    result (initial.relabel j) (next.relabel j) (parameter.relabel j) hc' hn' hr
  have he := valueUnique (repeatP transition) result (out.relabel j)
    (Fin.cons (tail.relabel j) (Fin.cons (next.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) ht ho'
  exact outputTransport (repeatP transition) result (out.relabel j)
    (Fin.cons (code.relabel j) (Fin.cons (initial.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) he hr

theorem actualParameterizedRawListRepeatFrontCons :
    InternalParameterizedApplicationStepCheckerTargets.ActualParameterizedRawListRepeatFrontCons := by
  intro body transition α Delta code head tail out initial next parameter
  let A := graph2 consCode code head tail ⊓ graph2 transition next initial parameter
  let P := repeatGraph transition out code initial parameter
  let Q := repeatGraph transition out tail next parameter
  have forward : Nonempty (Derivation body (P :: A :: Delta) Q) :=
    frontConsForward transition code head tail out initial next parameter
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body (Q :: A :: Delta) P) :=
    frontConsBackward transition code head tail out initial next parameter
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatProof
