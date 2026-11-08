module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationCommutationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalNumericIterationCommutationProof InternalListCodec InternalListCodecSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem frontSuccForward (transition : Program 1) (count out initial next : OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out count next)) := by
  apply programCases (repeatProgram transition) (Fin.cons count (Fin.cons initial Fin.elim0)) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,sucRelabel] at ho'
  have ht := repeatSuccRecover transition (count.relabel j)
    result (out.relabel j) (initial.relabel j) hr ho'
  exact commuteValue transition (count.relabel j) (initial.relabel j) (next.relabel j)
    result (out.relabel j) hn' hr ht

theorem frontSuccBackward (transition : Program 1) (count out initial next : OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out count next))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial)) := by
  apply programCases (repeatProgram transition) (Fin.cons (suc count) (Fin.cons initial Fin.elim0)) _
  intro β j Delta result hj hr
  simp only [repeatRename,sucRelabel]
  simp only [consTermRename,emptyRename,sucRelabel] at hr
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have ht := frontSuccForward transition (count.relabel j)
    result (initial.relabel j) (next.relabel j) hn' hr
  have he := valueUnique (repeatProgram transition) result (out.relabel j)
    (Fin.cons (count.relabel j) (Fin.cons (next.relabel j) Fin.elim0)) ht ho'
  exact outputTransport (repeatProgram transition) result (out.relabel j)
    (Fin.cons (suc (count.relabel j)) (Fin.cons (initial.relabel j) Fin.elim0)) he hr

theorem actualOriginalNumericIterationZero :
    InternalNumericIterationTargets.ActualOriginalNumericIterationZero := by
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

theorem actualOriginalNumericIterationFrontSuccessor :
    InternalNumericIterationTargets.ActualOriginalNumericIterationFrontSuccessor := by
  intro body transition α out count initial next
  let A := programGraph transition next (Fin.cons initial Fin.elim0)
  let P := repeatGraph transition out (suc count) initial
  let Q := repeatGraph transition out count next
  have forward : Nonempty (Derivation body [P,A] Q) :=
    frontSuccForward transition count out initial next
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q,A] P) :=
    frontSuccBackward transition count out initial next
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

theorem actualOriginalNumericIterationAdditionFusion :
    InternalNumericIterationTargets.ActualOriginalNumericIterationAdditionFusion :=
  InternalNumericIterationFusionProof.actualOriginalNumericIterationAdditionFusion

theorem actualOriginalNumericIterationFixedPoint :
    InternalNumericIterationTargets.ActualOriginalNumericIterationFixedPoint :=
  InternalNumericIterationFixedPointProof.actualOriginalNumericIterationFixedPoint

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
