module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalSquareRoot InternalSquareRootArithmetic InternalSquareRootSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalLessThanSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalArithmeticProgramsMultiplicationProof
open InternalRecursionGraphSuccessorIntroductionProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem successorCounterValue (n old : OTerm α) :
    Nonempty (Derivation body Gamma (programGraph successorCounter (suc n)
      (Fin.cons n (Fin.cons old Fin.elim0)))) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2)) (suc n)
    (Fin.cons n (Fin.cons old Fin.elim0)) (Fin.cons n Fin.elim0) (successorValue (Fin.cons n Fin.elim0))
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact projectionValue (0 : Fin 2) _

theorem successorRootValue (n old : OTerm α) :
    Nonempty (Derivation body Gamma (programGraph successorRoot (suc old)
      (Fin.cons n (Fin.cons old Fin.elim0)))) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection (1 : Fin 2)) (suc old)
    (Fin.cons n (Fin.cons old Fin.elim0)) (Fin.cons old Fin.elim0) (successorValue (Fin.cons old Fin.elim0))
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact projectionValue (1 : Fin 2) _

theorem nextSquareValue (n old : OTerm α) :
    Nonempty (Derivation body Gamma (programGraph nextSquare (square (suc old))
      (Fin.cons n (Fin.cons old Fin.elim0)))) := by
  apply compositionValue InternalArithmeticPrograms.multiplication
    (Fin.cons successorRoot (Fin.cons successorRoot Fin.elim0)) (square (suc old))
    (Fin.cons n (Fin.cons old Fin.elim0)) (Fin.cons (suc old) (Fin.cons (suc old) Fin.elim0))
    (multiplicationValue (suc old) (suc old))
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact successorRootValue n old
  · exact successorRootValue n old

theorem controlValue (n old out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (lessGraph out (suc n) (square (suc old))))) :
    Nonempty (Derivation body Gamma (programGraph belowNextSquare out
      (Fin.cons n (Fin.cons old Fin.elim0)))) := by
  apply compositionValue InternalLessThan.ltTest
    (Fin.cons successorCounter (Fin.cons nextSquare Fin.elim0)) out
    (Fin.cons n (Fin.cons old Fin.elim0)) (Fin.cons (suc n) (Fin.cons (square (suc old)) Fin.elim0)) hc
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact successorCounterValue n old
  · exact nextSquareValue n old

theorem stepRetain (n old : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF (suc n) (square (suc old))))) :
    Nonempty (Derivation body Gamma (programGraph step old (Fin.cons n (Fin.cons old Fin.elim0)))) :=
  successorBranchIntro belowNextSquare successorRoot (.projection (1 : Fin 2)) old z
    (Fin.cons n (Fin.cons old Fin.elim0))
    (controlValue n old (suc z) (acceptOfLess _ _ h)) (projectionValue (1 : Fin 2) _)

theorem stepAdvance (n old : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF (suc n) (square (suc old))).not)) :
    Nonempty (Derivation body Gamma (programGraph step (suc old) (Fin.cons n (Fin.cons old Fin.elim0)))) :=
  zeroBranchIntro belowNextSquare successorRoot (.projection (1 : Fin 2)) (suc old)
    (Fin.cons n (Fin.cons old Fin.elim0))
    (controlValue n old z (rejectOfNotLess _ _ h)) (successorRootValue n old)

theorem rootZero : Nonempty (Derivation body Gamma (rootGraph (z : OTerm α) z)) :=
  recursionZeroValue .zero step z Fin.elim0 (zeroValue Fin.elim0)

theorem rootNext (n old out : OTerm α)
    (hg : Nonempty (Derivation body Gamma (rootGraph old n)))
    (hs : Nonempty (Derivation body Gamma (programGraph step out (Fin.cons n (Fin.cons old Fin.elim0))))) :
    Nonempty (Derivation body Gamma (rootGraph out (suc n))) :=
  recursionSuccessorIntroduction Gamma (OrdinaryArithmetic.graphFormula .zero)
    (OrdinaryArithmetic.graphFormula step) out n old Fin.elim0 hg hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootStepProof
