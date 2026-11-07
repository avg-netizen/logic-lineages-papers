module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonProof InternalBetaBoundaryProof InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem intervalConflict (s t n : OTerm α)
    (hs : Nonempty (Derivation body Gamma (interval s n)))
    (ht : Nonempty (Derivation body Gamma (interval t n)))
    (hst : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma ⊥) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  have hm := nextSquareWeak s t hst
  have hu := strictWeakTrans n (square (suc s)) (square t)
    ⟨Derivation.conjunctionRight hs⟩ hm
  obtain ⟨loop⟩ := strictWeakTrans n (square t) n hu ⟨Derivation.conjunctionLeft ht⟩
  obtain ⟨hn⟩ := actualOriginalOrderIrreflexivity body α n
  exact ⟨Derivation.implicationElimination (weakenClosed hn Gamma) loop⟩

theorem intervalUnique (s t n : OTerm α)
    (hs : Nonempty (Derivation body Gamma (interval s n)))
    (ht : Nonempty (Derivation body Gamma (interval t n))) :
    Nonempty (Derivation body Gamma (eqn s t)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  obtain ⟨cmp⟩ := actualOriginalComparison body α s t
  have hc := compareView (weakenClosed cmp Gamma)
  have hl : Nonempty (Derivation body (ltF s t :: Gamma) (eqn s t)) := by
    obtain ⟨contra⟩ := intervalConflict s t n ⟨addHyp hs _⟩ ⟨addHyp ht _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.explosion contra⟩
  have hr : Nonempty (Derivation body (ltF t s :: Gamma) (eqn s t)) := by
    obtain ⟨contra⟩ := intervalConflict t s n ⟨addHyp ht _⟩ ⟨addHyp hs _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.explosion contra⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have he : Derivation body Gamma ((eqn s t).imp (eqn s t)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hp : Derivation body Gamma ((eqn s t ⊔ ltF t s).imp (eqn s t)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hp⟩

def intervalZero : Derivation body Gamma (interval (z : OTerm α) z) :=
  Derivation.conjunctionIntroduction
    (orderLeft (suc z) (symm (mulZero z)) (zeroLessSuccessor z))
    (orderLeft (square (suc z)) (mulZero z) (successorSquareStrict z))

/-- The old upper bound and discrete boundary force exact equality at a
crossing. No inequality is reflected from the standard naturals. -/
theorem boundaryCrossing (s n : OTerm α)
    (h : Nonempty (Derivation body Gamma (interval s n)))
    (hn : Nonempty (Derivation body Gamma (ltF (suc n) (square (suc s))).not)) :
    Nonempty (Derivation body Gamma (eqn (suc n) (square (suc s)))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := hn
  obtain ⟨d⟩ := actualDiscreteOrderBoundary body α n (square (suc s))
  rw [onEquality] at d
  have hd := Derivation.implicationElimination (weakenClosed d Gamma) (Derivation.conjunctionRight h)
  exact ⟨disjunctionElimination hd
    (Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp hn _) (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

theorem intervalRetain (s n : OTerm α)
    (h : Nonempty (Derivation body Gamma (interval s n)))
    (hn : Nonempty (Derivation body Gamma (ltF (suc n) (square (suc s))))) :
    Nonempty (Derivation body Gamma (interval s (suc n))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := hn
  obtain ⟨lower⟩ := rightSuccessor (square s) (suc n) ⟨Derivation.conjunctionLeft h⟩
  exact ⟨Derivation.conjunctionIntroduction lower hn⟩

theorem intervalAdvance (s n : OTerm α)
    (h : Nonempty (Derivation body Gamma (interval s n)))
    (hn : Nonempty (Derivation body Gamma (ltF (suc n) (square (suc s))).not)) :
    Nonempty (Derivation body Gamma (interval (suc s) (suc n))) := by
  obtain ⟨edge⟩ := boundaryCrossing s n h hn
  exact ⟨Derivation.conjunctionIntroduction (equalToNext (symm edge))
    (orderLeft (square (suc (suc s))) (symm edge) (successorSquareStrict (suc s)))⟩

theorem actualSuccessorSquareExpansion : InternalSquareRootArithmeticTargets.ActualSuccessorSquareExpansion := by
  intro body α s
  rw [InternalSquareRootArithmeticTargets.eqF,onEquality]
  exact ⟨successorSquareExpansion s⟩
theorem actualSuccessorSquareStrict : InternalSquareRootArithmeticTargets.ActualSuccessorSquareStrict := by
  intro body α s
  exact ⟨successorSquareStrict s⟩
theorem actualSquareStrictMonotonicity : InternalSquareRootArithmeticTargets.ActualSquareStrictMonotonicity := by
  intro body α s t
  obtain ⟨h⟩ := squareStrictMonotonicity (body := body) (Gamma := [ltF s t]) s t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
theorem actualSquareIntervalZero : InternalSquareRootArithmeticTargets.ActualSquareIntervalZero := by
  intro body α
  exact ⟨intervalZero⟩
theorem actualSquareIntervalUniqueness : InternalSquareRootArithmeticTargets.ActualSquareIntervalUniqueness := by
  intro body α s t n
  let p := interval s n ⊓ interval t n
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := intervalUnique s t n ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  rw [InternalSquareRootArithmeticTargets.eqF,onEquality]
  exact ⟨Derivation.implicationIntroduction d⟩
theorem actualSquareBoundaryCrossing : InternalSquareRootArithmeticTargets.ActualSquareBoundaryCrossing := by
  intro body α s n
  let p := interval s n ⊓ (ltF (suc n) (square (suc s))).not
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := boundaryCrossing s n ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  rw [InternalSquareRootArithmeticTargets.eqF,onEquality]
  exact ⟨Derivation.implicationIntroduction d⟩
theorem actualSquareIntervalRetain : InternalSquareRootArithmeticTargets.ActualSquareIntervalRetain := by
  intro body α s n
  let p := interval s n ⊓ ltF (suc n) (square (suc s))
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := intervalRetain s n ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩
theorem actualSquareIntervalAdvance : InternalSquareRootArithmeticTargets.ActualSquareIntervalAdvance := by
  intro body α s n
  let p := interval s n ⊓ (ltF (suc n) (square (suc s))).not
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := intervalAdvance s n ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticProof
