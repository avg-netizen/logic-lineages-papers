module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem oneValue (xs : Fin 0 → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.one (suc z) xs)) := by
  apply compositionValue .succ (fun _ : Fin 1 => .zero) (suc z) xs (fun _ => z)
  · exact successorValue (fun _ : Fin 1 => (z : OrdinaryArithmetic.Term α))
  · intro i
    exact zeroValue xs

theorem zeroStepValue (xs : Fin 2 → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.zeroStep z xs)) := by
  apply compositionValue .zero Fin.elim0 z xs Fin.elim0
  · exact zeroValue _
  · intro i
    exact Fin.elim0 i

theorem zeroTestZeroValue :
    Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest (suc z) (Fin.cons z Fin.elim0))) :=
  recursionZeroValue _ _ (suc z) Fin.elim0 (oneValue _)

theorem zeroTestSuccessorValue (t : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest z (Fin.cons (suc t) Fin.elim0))) := by
  apply recursionSuccessorValue GorbowPRInternalControl.one GorbowPRInternalControl.zeroStep
    z t Fin.elim0
  intro β j Delta v _
  simp only [zRelabel]
  exact zeroStepValue _

theorem conditionalZeroValue (a b : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional a
      (Fin.cons z (Fin.cons a (Fin.cons b Fin.elim0))))) :=
  recursionZeroValue (.projection (0 : Fin 2)) (.projection (3 : Fin 4))
    a (Fin.cons a (Fin.cons b Fin.elim0)) (projectionValue (0 : Fin 2) (Fin.cons a (Fin.cons b Fin.elim0)))

theorem conditionalSuccessorValue (t a b : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional b
      (Fin.cons (suc t) (Fin.cons a (Fin.cons b Fin.elim0))))) := by
  apply recursionSuccessorValue (.projection (0 : Fin 2)) (.projection (3 : Fin 4))
    b t (Fin.cons a (Fin.cons b Fin.elim0))
  intro β j Delta v _
  simp only [consTermRename,emptyRename]
  exact projectionValue (3 : Fin 4) (Fin.cons (t.relabel j)
    (Fin.cons v (Fin.cons (a.relabel j) (Fin.cons (b.relabel j) Fin.elim0))))

theorem equalsOneZeroValue :
    Nonempty (Derivation body Gamma
      (programGraph GorbowVerifierNormalization.equalsOne z (Fin.cons z Fin.elim0))) :=
  recursionZeroValue .zero GorbowVerifierNormalization.equalsOneStep z Fin.elim0 (zeroValue _)

/-- The step observes the previous counter, not the previous result. -/
theorem equalsOneSuccessorValue (out t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest out (Fin.cons t Fin.elim0)))) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowVerifierNormalization.equalsOne out (Fin.cons (suc t) Fin.elim0))) := by
  apply recursionSuccessorValue .zero GorbowVerifierNormalization.equalsOneStep out t Fin.elim0
  intro β j Delta v hj
  simp only [emptyRename]
  have h' := renameInto h j Delta hj
  simp only [programRename,consTermRename,emptyRename] at h'
  apply compositionValue GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => .projection (0 : Fin 2))
    (out.relabel j) (Fin.cons (t.relabel j) (Fin.cons v Fin.elim0))
    (Fin.cons (t.relabel j) Fin.elim0) h'
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact projectionValue (0 : Fin 2) (Fin.cons (t.relabel j) (Fin.cons v Fin.elim0))

theorem equalsOneOneValue :
    Nonempty (Derivation body Gamma
      (programGraph GorbowVerifierNormalization.equalsOne (suc z) (Fin.cons (suc z) Fin.elim0))) :=
  equalsOneSuccessorValue (suc z) z zeroTestZeroValue

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphValueProof
