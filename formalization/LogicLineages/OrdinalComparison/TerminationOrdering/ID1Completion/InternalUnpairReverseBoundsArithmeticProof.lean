module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalUnpairReverse
open InternalUnpairReverseSyntaxProof InternalUnpairArithmeticProof InternalControlGraphSupportProof
open InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalMultiplicationLeftSuccessorProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonProof InternalLeastNumberProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalBetaDivisionSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rightWeakAdd (a b : OTerm α) :
    Nonempty (Derivation body Gamma (ltF b (suc (add a b)))) := by
  obtain ⟨h⟩ := leftWeakAdd (body := body) (Gamma := Gamma) b a
  exact ⟨orderRight b (congSuc (commutativity b a)) h⟩

theorem weakTrans (s t u : OTerm α)
    (hs : Nonempty (Derivation body Gamma (ltF s (suc t))))
    (ht : Nonempty (Derivation body Gamma (ltF t (suc u)))) :
    Nonempty (Derivation body Gamma (ltF s (suc u))) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  obtain ⟨split⟩ := actualRightSuccessorSplit body α s t
  rw [onEquality] at split
  have hd := Derivation.implicationElimination (weakenClosed split Gamma) hs
  have hl : Nonempty (Derivation body (ltF s t :: Gamma) (ltF s (suc u))) :=
    rightSuccessor s u (strictWeakTrans s t u
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp ht _⟩)
  obtain ⟨hl⟩ := hl
  have he : Derivation body (eqn s t :: Gamma) (ltF s (suc u)) :=
    orderLeft (suc u) (symm (Derivation.hypothesis List.mem_cons_self)) (addHyp ht _)
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction he)⟩

/-- The original zero/successor split and multiplication recursion prove
s≤s*s internally, including the exceptional zero case. -/
theorem squareSelfWeak (s : OTerm α) :
    Nonempty (Derivation body Gamma (ltF s (suc (square s)))) := by
  apply zeroSuccessorCases Gamma s _
  · have he : Derivation body (eqn s z :: Gamma) (eqn s z) :=
      Derivation.hypothesis List.mem_cons_self
    have sqe := trans (squareCongr he) (mulZero z)
    exact ⟨equalToNext (trans he (symm sqe))⟩
  · intro β j Delta v _ ⟨he⟩
    simp only [orderRename,sucRelabel,square,mulRelabel]
    obtain ⟨hb⟩ := rightWeakAdd (body := body) (Gamma := Delta) (mul v (suc v)) (suc v)
    have h1 := orderRight (suc v) (congSuc (symm (leftSuccessorMultiplication v (suc v)))) hb
    have h2 := orderLeft (suc (square (suc v))) (symm he) h1
    exact ⟨orderRight (s.relabel j) (congSuc (squareCongr (symm he))) h2⟩

def boundsTransport (x y : OTerm α) {n m : OTerm α}
    (he : Derivation body Gamma (eqn n m)) (h : Derivation body Gamma (coordinateBounds n x y)) :
    Derivation body Gamma (coordinateBounds m x y) :=
  Derivation.conjunctionIntroduction
    (orderRight x (congSuc he) (Derivation.conjunctionLeft h))
    (orderRight y (congSuc he) (Derivation.conjunctionRight h))

theorem lessBranchBounds (x y : OTerm α) :
    Nonempty (Derivation body Gamma (coordinateBounds (add (square y) x) x y)) := by
  obtain ⟨hx⟩ := rightWeakAdd (body := body) (Gamma := Gamma) (square y) x
  obtain ⟨hy⟩ := weakTrans y (square y) (add (square y) x)
    (squareSelfWeak y) (leftWeakAdd (square y) x)
  exact ⟨Derivation.conjunctionIntroduction hx hy⟩

theorem nonLessBranchBounds (x y : OTerm α) :
    Nonempty (Derivation body Gamma (coordinateBounds (add (add (square x) x) y) x y)) := by
  obtain ⟨hx⟩ := weakTrans (body := body) (Gamma := Gamma) x (add (square x) x)
    (add (add (square x) x) y) (rightWeakAdd (square x) x) (leftWeakAdd (add (square x) x) y)
  obtain ⟨hy⟩ := rightWeakAdd (body := body) (Gamma := Gamma) (add (square x) x) y
  exact ⟨Derivation.conjunctionIntroduction hx hy⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
