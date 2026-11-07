module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open InternalEqualityTestCompositionProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rejectForwardOrder (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma (equalityGraph z x y)) := by
  apply orderCases Gamma x y _ h
  intro β j Delta gap _ he
  simp only [equalityGraphRename,zRelabel]
  exact rejectForwardGap (x.relabel j) (y.relabel j) gap he

theorem rejectBackwardOrder (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF y x))) :
    Nonempty (Derivation body Gamma (equalityGraph z x y)) := by
  apply orderCases Gamma y x _ h
  intro β j Delta gap _ he
  simp only [equalityGraphRename,zRelabel]
  exact rejectBackwardGap (x.relabel j) (y.relabel j) gap he

/-- Internal trichotomy and graph functionality exclude each strict case.
Standard evaluation calibration is not imported or used by this proof. -/
theorem equalityOfAcceptance (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (equalityGraph (suc z) x y))) :
    Nonempty (Derivation body Gamma (eqn x y)) := by
  obtain ⟨h⟩ := h
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Gamma)
  have hl : Nonempty (Derivation body (ltF x y :: Gamma) (eqn x y)) := by
    have hz := rejectForwardOrder (body := body) (Gamma := ltF x y :: Gamma) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique equalityTest (suc z) z (Fin.cons x (Fin.cons y Fin.elim0))
      ⟨addHyp h _⟩ hz
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  have hr : Nonempty (Derivation body (ltF y x :: Gamma) (eqn x y)) := by
    have hz := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Gamma) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique equalityTest (suc z) z (Fin.cons x (Fin.cons y Fin.elim0))
      ⟨addHyp h _⟩ hz
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have he : Derivation body Gamma ((eqn x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hrest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

theorem actualOriginalEqualityAcceptance : InternalEqualityTestTargets.ActualOriginalEqualityAcceptance := by
  intro body α x y
  obtain ⟨hf⟩ := equalityOfAcceptance (body := body) (Gamma := [equalityGraph (suc z) x y]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := equalityOfEqual (body := body) (Gamma := [eqn x y]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simp only [equalEqn]
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
