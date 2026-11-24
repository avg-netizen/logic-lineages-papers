module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundChargeArithmeticProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof
open ID1Completion.InternalTagArithmeticSupportProof
open ID1Completion.InternalOriginalOrderSyntaxProof
open ID1Completion.InternalSquareRootArithmeticSupportProof
open ID1Completion.InternalAdditionLawsProof ID1Completion.InternalUnpairArithmeticProof
open ID1Completion.InternalPositiveUnfoldingSupportProof
open NumberedWindowInternalThinUncoveredCount (bounded)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The next three lemmas use the arithmetic part of the retained finite-descent proof. -/
theorem fromWeak (a b : OTerm alpha) (h : Nonempty (Derivation body Delta (ltF a (suc b)))) :
    Nonempty (Derivation body Delta (bounded a b)) := by
  obtain ⟨hd⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body alpha a b
  rw [InternalSourceInversionSupportProof.onEquality] at hd
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed hd Delta) h⟩

theorem boundTrans (a b c : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (bounded a b)))
    (hbc : Nonempty (Derivation body Delta (bounded b c))) :
    Nonempty (Derivation body Delta (bounded a c)) :=
  fromWeak a c (InternalUnpairReverseBoundsArithmeticProof.weakTrans a b c
    (NumberedWindowInternalThinUncoveredCountOrderProof.strictNext a b hab) (NumberedWindowInternalThinUncoveredCountOrderProof.strictNext b c hbc))

theorem budgetStep (elapsed old remaining initial : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (ltF remaining old)))
    (hb : Nonempty (Derivation body Delta (bounded (add elapsed old) initial))) :
    Nonempty (Derivation body Delta (bounded (add (suc elapsed) remaining) initial)) := by
  obtain ⟨ha⟩ := addStrictLeft elapsed remaining old hd
  obtain ⟨hdisc⟩ := InternalBetaBoundaryProof.actualDiscreteOrderBoundary body alpha
    (add elapsed remaining) (add elapsed old)
  rw [InternalSourceInversionSupportProof.onEquality] at hdisc
  have hstep : Nonempty (Derivation body Delta
      (bounded (suc (add elapsed remaining)) (add elapsed old))) :=
    ⟨Derivation.implicationElimination (weakenClosed hdisc Delta) ha⟩
  have htransport := NumberedWindowInternalThinUncoveredCountOrderProof.transport (suc (add elapsed remaining)) (add elapsed old)
    (add (suc elapsed) remaining) (add elapsed old)
    ⟨symm (leftSuccessor elapsed remaining)⟩ ⟨refl _⟩ hstep
  exact boundTrans (add (suc elapsed) remaining) (add elapsed old) initial htransport hb

end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundChargeArithmeticProof
