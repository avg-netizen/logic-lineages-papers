module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalPairingSumBounds
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Adding the same original arithmetic term preserves weak order internally. -/
theorem addWeakLeft (a s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (weakBound s t))) :
    Nonempty (Derivation body Gamma (weakBound (add a s) (add a t))) := by
  obtain ⟨h⟩ := addStrictLeft a s (suc t) h
  exact ⟨orderRight (add a s) (addSucc a t) h⟩

theorem addWeakRight (s t a : OTerm α)
    (h : Nonempty (Derivation body Gamma (weakBound s t))) :
    Nonempty (Derivation body Gamma (weakBound (add s a) (add t a))) := by
  obtain ⟨h⟩ := addWeakLeft a s t h
  exact ⟨orderRight (add s a) (congSuc (commutativity a t))
    (orderLeft (suc (add a t)) (commutativity a s) h)⟩

theorem successorWeak (s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (weakBound s t))) :
    Nonempty (Derivation body Gamma (weakBound (suc s) (suc t))) := by
  obtain ⟨h⟩ := addWeakLeft (suc z) s t h
  have es : Derivation body Gamma (eqn (add (suc z) s) (suc s)) :=
    trans (leftSuccessor z s) (congSuc (leftZero s))
  have et : Derivation body Gamma (eqn (add (suc z) t) (suc t)) :=
    trans (leftSuccessor z t) (congSuc (leftZero t))
  exact ⟨orderRight (suc s) (congSuc et)
    (orderLeft (suc (add (suc z) t)) es h)⟩

/-- This includes y=0: the accepted internal square-self bound has no positivity premise. -/
theorem lessBranchSum (x y : OTerm α) :
    Nonempty (Derivation body Gamma (weakBound (add x y) (add (square y) x))) := by
  obtain ⟨h⟩ := addWeakLeft (body := body) (Gamma := Gamma) x y (square y) (squareSelfWeak y)
  exact ⟨orderRight (add x y) (congSuc (commutativity x (square y))) h⟩

theorem nonLessBranchSum (x y : OTerm α) :
    Nonempty (Derivation body Gamma
      (weakBound (add x y) (add (add (square x) x) y))) :=
  addWeakRight x (add (square x) x) y (rightWeakAdd (square x) x)

/-- Literal PA addition laws identify the two child counts with two plus their payload sum. -/
def childSumExpansion (fp ap : OTerm α) :
    Derivation body Gamma (eqn (childFuelSum fp ap) (add (suc (suc z)) (add fp ap))) := by
  have hc : Derivation body Gamma (eqn (childFuelSum fp ap) (suc (suc (add fp ap)))) :=
    trans (leftSuccessor fp (suc ap)) (congSuc (addSucc fp ap))
  have ht : Derivation body Gamma
      (eqn (add (suc (suc z)) (add fp ap)) (suc (suc (add fp ap)))) :=
    trans (leftSuccessor (suc z) (add fp ap))
      (congSuc (trans (leftSuccessor z (add fp ap)) (congSuc (leftZero (add fp ap)))))
  exact trans hc (symm ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
