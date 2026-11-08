module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatCommutationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRepeat InternalRawListRepeatSyntaxProof InternalRawListRepeatSupportProof
open InternalRawListRepeatCommutationProof InternalListCodec InternalListCodecSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem frontConsForward (transition : Program 1) (code head tail out initial next : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out code initial))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out tail next)) := by
  apply programCases (repeatProgram transition) (Fin.cons tail (Fin.cons initial Fin.elim0)) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have ht := repeatConsRecover transition (code.relabel j) (head.relabel j) (tail.relabel j)
    result (out.relabel j) (initial.relabel j) hc' hr ho'
  exact commuteValue transition (tail.relabel j) (initial.relabel j) (next.relabel j)
    result (out.relabel j) hn' hr ht

theorem frontConsBackward (transition : Program 1) (code head tail out initial next : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out tail next))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code initial)) := by
  apply programCases (repeatProgram transition) (Fin.cons code (Fin.cons initial Fin.elim0)) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have ht := frontConsForward transition (code.relabel j) (head.relabel j) (tail.relabel j)
    result (initial.relabel j) (next.relabel j) hc' hn' hr
  have he := valueUnique (repeatProgram transition) result (out.relabel j)
    (Fin.cons (tail.relabel j) (Fin.cons (next.relabel j) Fin.elim0)) ht ho'
  exact outputTransport (repeatProgram transition) result (out.relabel j)
    (Fin.cons (code.relabel j) (Fin.cons (initial.relabel j) Fin.elim0)) he hr

theorem actualOriginalRawListRepeatZero :
    InternalRawListRepeatTargets.ActualOriginalRawListRepeatZero := by
  intro body transition α out initial
  let P := repeatGraph transition out z initial
  let Q := equal out initial
  have forward : Nonempty (Derivation body [P] Q) := by
    change Nonempty (Derivation body [P] (equal out initial))
    rw [equalEqn]
    exact repeatZeroRecover transition out initial ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q] P) := by
    have hq : Derivation body [Q] (eqn out initial) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (repeatProgram transition) initial out
      (Fin.cons z (Fin.cons initial Fin.elim0)) ⟨symm hq⟩ (repeatZeroValue transition initial)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem actualOriginalRawListRepeatCons :
    InternalRawListRepeatTargets.ActualOriginalRawListRepeatCons := by
  intro body transition α code head tail tailResult out initial
  let A := consGraph code head tail ⊓ repeatGraph transition tailResult tail initial
  let P := repeatGraph transition out code initial
  let Q := programGraph transition out (Fin.cons tailResult Fin.elim0)
  have forward : Nonempty (Derivation body [P,A] Q) :=
    repeatConsRecover transition code head tail tailResult out initial
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q,A] P) :=
    repeatConsValue transition code head tail tailResult out initial
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

theorem actualOriginalRawListRepeatFrontCons :
    InternalRawListRepeatTargets.ActualOriginalRawListRepeatFrontCons := by
  intro body transition α code head tail out initial next
  let A := consGraph code head tail ⊓ programGraph transition next (Fin.cons initial Fin.elim0)
  let P := repeatGraph transition out code initial
  let Q := repeatGraph transition out tail next
  have forward : Nonempty (Derivation body [P,A] Q) :=
    frontConsForward transition code head tail out initial next
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q,A] P) :=
    frontConsBackward transition code head tail out initial next
      ⟨Derivation.conjunctionLeft (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.conjunctionRight (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
