module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalArithmeticProgramsSupportProof InternalLeastNumberProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonProof InternalBetaTotalityProof InternalControlGraphSupportProof
open InternalControlGraphChoiceProof InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalUnpairArithmeticProof InternalUnpairReverseBoundsArithmeticProof
open InternalPairingSumBoundsArithmeticProof InternalPairingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem withHyp {phi : Formula α} (h : Nonempty (Derivation body Gamma phi)) (p : Formula α) :
    Nonempty (Derivation body (p :: Gamma) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

theorem formulaCases (p psi : Formula α)
    (hp : Nonempty (Derivation body (p :: Gamma) psi))
    (hn : Nonempty (Derivation body (p.not :: Gamma) psi)) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction hp) (Derivation.implicationIntroduction hn)⟩

/-- This is the original arithmetic successor split, not a semantic case split. -/
theorem weakCases (s t : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (ltF s (suc t))))
    (hl : Nonempty (Derivation body (ltF s t :: Gamma) psi))
    (he : Nonempty (Derivation body (eqn s t :: Gamma) psi)) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨split⟩ := actualRightSuccessorSplit body α s t
  rw [onEquality] at split
  obtain ⟨hl⟩ := hl
  obtain ⟨he⟩ := he
  exact ⟨disjunctionElimination
    (Derivation.implicationElimination (InternalPositiveUnfoldingSupportProof.weakenClosed split Gamma) h)
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction he)⟩

theorem strictWeakConflict (s t : OrdinaryArithmetic.Term α) (psi : Formula α)
    (hs : Nonempty (Derivation body Gamma (ltF s t)))
    (ht : Nonempty (Derivation body Gamma (ltF t (suc s)))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hh⟩ := strictWeakTrans s t s hs ht
  obtain ⟨hi⟩ := actualOriginalOrderIrreflexivity body α s
  exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalPositiveUnfoldingSupportProof.weakenClosed hi Gamma) hh)⟩

theorem weakStrictTrans (s t u : OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma (ltF s (suc t))))
    (ht : Nonempty (Derivation body Gamma (ltF t u))) :
    Nonempty (Derivation body Gamma (ltF s u)) := by
  apply weakCases s t _ hs
  · exact strictTrans s t u ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht _)
  · obtain ⟨ht⟩ := ht
    exact ⟨orderLeft u (symm (Derivation.hypothesis List.mem_cons_self)) (addHyp ht _)⟩

theorem squareWeak (s t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (ltF s (suc t)))) :
    Nonempty (Derivation body Gamma (ltF (square s) (suc (square t)))) := by
  apply weakCases s t _ h
  · exact rightSuccessor _ _ (squareStrictMonotonicity s t
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · exact ⟨equalToNext (squareCongr (Derivation.hypothesis List.mem_cons_self))⟩

theorem addStrictRight (s t a : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (add s a) (add t a))) := by
  obtain ⟨h⟩ := addStrictLeft a s t h
  exact ⟨orderRight (add s a) (InternalAdditionCancellationProof.commutativity a t)
    (orderLeft (add a t) (InternalAdditionCancellationProof.commutativity a s) h)⟩

theorem addWeakBoth (s t u v : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (ltF s (suc t))))
    (k : Nonempty (Derivation body Gamma (ltF u (suc v)))) :
    Nonempty (Derivation body Gamma (ltF (add s u) (suc (add t v)))) :=
  weakTrans (add s u) (add t u) (add t v)
    (addWeakRight s t u h) (addWeakLeft t u v k)

theorem weakTransport (s t u v : OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma (eqn s u)))
    (ht : Nonempty (Derivation body Gamma (eqn t v)))
    (h : Nonempty (Derivation body Gamma (ltF u (suc v)))) :
    Nonempty (Derivation body Gamma (ltF s (suc t))) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  obtain ⟨h⟩ := h
  exact ⟨orderRight s (congSuc (symm ht)) (orderLeft (suc v) (symm hs) h)⟩

theorem strictTransport (s t u v : OrdinaryArithmetic.Term α)
    (hs : Nonempty (Derivation body Gamma (eqn s u)))
    (ht : Nonempty (Derivation body Gamma (eqn t v)))
    (h : Nonempty (Derivation body Gamma (ltF u v))) :
    Nonempty (Derivation body Gamma (ltF s t)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  obtain ⟨h⟩ := h
  exact ⟨orderRight s (symm ht) (orderLeft v (symm hs) h)⟩

theorem lessValue (p x y : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma (eqn p (add (square y) x))) :=
  valueUnique InternalPairing.pairing p (add (square y) x)
    (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfLess x y h)

theorem nonLessValue (p x y : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (binaryGraph InternalPairing.pairing p x y)))
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma (eqn p (add (add (square x) x) y))) :=
  valueUnique InternalPairing.pairing p (add (add (square x) x) y)
    (Fin.cons x (Fin.cons y Fin.elim0)) hp (pairingOfNotLess x y h)

/-- Crossing the pairing diagonal is controlled by the exact successor-square
interval already proved for the original polynomial branch. -/
theorem rightCrossing (x y v : OrdinaryArithmetic.Term α)
    (hy : Nonempty (Derivation body Gamma (ltF x y).not))
    (hv : Nonempty (Derivation body Gamma (ltF x v))) :
    Nonempty (Derivation body Gamma
      (ltF (add (add (square x) x) y) (add (square v) x))) := by
  obtain ⟨hi⟩ := nonLessPairInterval x y hy
  exact strictWeakTrans _ (square v) _
    (strictWeakTrans _ (square (suc x)) (square v)
      ⟨Derivation.conjunctionRight hi⟩ (nextSquareWeak x v hv))
    (leftWeakAdd (square v) x)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof.rightCrossing
