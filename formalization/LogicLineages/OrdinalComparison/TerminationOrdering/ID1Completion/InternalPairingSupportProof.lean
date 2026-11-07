module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalPairing InternalArithmeticPrograms
open InternalArithmeticProgramsSupportProof InternalArithmeticProgramsMultiplicationProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalLessThanSupportProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof InternalMultiplicationLawsProof
open InternalOriginalOrderSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem squareFirstValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph squareFirst (mul x x) x y)) := by
  apply compositionValue multiplication (fun _ : Fin 2 => .projection (0 : Fin 2))
    (mul x x) (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons x (Fin.cons x Fin.elim0))
    (multiplicationValue x x)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact projectionValue (0 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))
  · exact projectionValue (0 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem squareSecondValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph squareSecond (mul y y) x y)) := by
  apply compositionValue multiplication (fun _ : Fin 2 => .projection (1 : Fin 2))
    (mul y y) (Fin.cons x (Fin.cons y Fin.elim0)) (Fin.cons y (Fin.cons y Fin.elim0))
    (multiplicationValue y y)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact projectionValue (1 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))
  · exact projectionValue (1 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem squareFirstPlusFirstValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph squareFirstPlusFirst (add (mul x x) x) x y)) := by
  apply compositionValue addition
    (Fin.cons squareFirst (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))
    (add (mul x x) x) (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons (mul x x) (Fin.cons x Fin.elim0)) (additionValue (mul x x) x)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact squareFirstValue x y
  · exact projectionValue (0 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem nonLessBranchValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph nonLessBranch (add (add (mul x x) x) y) x y)) := by
  apply compositionValue addition
    (Fin.cons squareFirstPlusFirst (Fin.cons (.projection (1 : Fin 2)) Fin.elim0))
    (add (add (mul x x) x) y) (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons (add (mul x x) x) (Fin.cons y Fin.elim0)) (additionValue (add (mul x x) x) y)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact squareFirstPlusFirstValue x y
  · exact projectionValue (1 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem lessBranchValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph lessBranch (add (mul y y) x) x y)) := by
  apply compositionValue addition
    (Fin.cons squareSecond (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))
    (add (mul y y) x) (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons (mul y y) (Fin.cons x Fin.elim0)) (additionValue (mul y y) x)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact squareSecondValue x y
  · exact projectionValue (0 : Fin 2) (Fin.cons x (Fin.cons y Fin.elim0))

theorem pairingOfLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma (binaryGraph pairing (add (mul y y) x) x y)) :=
  successorBranchIntro InternalLessThan.ltTest nonLessBranch lessBranch (add (mul y y) x) z
    (Fin.cons x (Fin.cons y Fin.elim0)) (acceptOfLess x y h) (lessBranchValue x y)

theorem pairingOfNotLess (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma (binaryGraph pairing (add (add (mul x x) x) y) x y)) :=
  zeroBranchIntro InternalLessThan.ltTest nonLessBranch lessBranch (add (add (mul x x) x) y)
    (Fin.cons x (Fin.cons y Fin.elim0)) (rejectOfNotLess x y h) (nonLessBranchValue x y)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
