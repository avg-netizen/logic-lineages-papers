module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof
open InternalRawListRecursion InternalRawListRecursionProof InternalRawListRecursionSyntaxProof
open InternalListCodec InternalListCodecSupportProof SourceComputabilityFormulaSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem repeatZeroValue (transition : Program 1) (initial : OTerm α) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial z initial)) :=
  recursionZeroValue (.projection 0) (repeatStep transition) initial (Fin.cons initial Fin.elim0)
    (projectionValue 0 (Fin.cons initial Fin.elim0))

theorem repeatZeroRecover (transition : Program 1) (out initial : OTerm α)
    (h : Nonempty (Derivation body Gamma (repeatGraph transition out z initial))) :
    Nonempty (Derivation body Gamma (eqn out initial)) :=
  valueUnique (repeatProgram transition) out initial (Fin.cons z (Fin.cons initial Fin.elim0))
    h (repeatZeroValue transition initial)

theorem repeatStepValue (transition : Program 1) (head result initial out : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (programGraph (repeatStep transition) out
      (Fin.cons head (Fin.cons result (Fin.cons initial Fin.elim0))))) := by
  apply compositionValue transition (fun _ : Fin 1 => .projection 1) out
    (Fin.cons head (Fin.cons result (Fin.cons initial Fin.elim0)))
    (Fin.cons result Fin.elim0) h
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact projectionValue 1 (Fin.cons head (Fin.cons result (Fin.cons initial Fin.elim0)))

theorem repeatSuccValue (transition : Program 1)
    (count result out initial : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result count initial)))
    (ht : Nonempty (Derivation body Gamma
      (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial)) :=
  InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction
    Gamma (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula (repeatStep transition)) out count result
    (Fin.cons initial Fin.elim0) hr (repeatStepValue transition count result initial out ht)

theorem repeatSuccRecover (transition : Program 1)
    (count result out initial : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result count initial)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial))) :
    Nonempty (Derivation body Gamma
      (programGraph transition out (Fin.cons result Fin.elim0))) := by
  apply programCases transition (Fin.cons result Fin.elim0) _
  intro β j Delta value hj hv
  simp only [programRename,consTermRename,emptyRename]
  simp only [consTermRename,emptyRename] at hv
  have hr' := renameInto hr j Delta hj
  rw [repeatRename] at hr'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,sucRelabel] at ho'
  have hvalue := repeatSuccValue transition (count.relabel j)
    (result.relabel j) value (initial.relabel j) hr' hv
  have he := valueUnique (repeatProgram transition) value (out.relabel j)
    (Fin.cons (suc (count.relabel j)) (Fin.cons (initial.relabel j) Fin.elim0)) hvalue ho'
  exact outputTransport transition value (out.relabel j) (Fin.cons (result.relabel j) Fin.elim0) he hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
