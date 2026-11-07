module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalLessThan
open InternalLessThanSupportProof InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem actualOriginalLessThanGraph : InternalLessThanTargets.ActualOriginalLessThanGraph := by
  intro body α out x y
  have hy : Nonempty (Derivation body [] ((ltF x y).imp (lessGraph (suc z) x y))) := by
    obtain ⟨d⟩ := acceptOfLess (body := body) (Gamma := [ltF x y]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hn : Nonempty (Derivation body [] ((ltF x y).not.imp (lessGraph z x y))) := by
    obtain ⟨d⟩ := rejectOfNotLess (body := body) (Gamma := [(ltF x y).not]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  simpa only [lessThanSpec,strictLess,equalEqn] using
    (choiceEquation ltTest out (suc z) z (Fin.cons x (Fin.cons y Fin.elim0)) (ltF x y) hy hn)

theorem lessOfAcceptance (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (lessGraph (suc z) x y))) :
    Nonempty (Derivation body Gamma (ltF x y)) := by
  obtain ⟨d⟩ := actualOriginalLessThanGraph body α (suc z) x y
  obtain ⟨h⟩ := h
  have ds := Derivation.implicationElimination
    (weakenClosed (Derivation.conjunctionLeft d) Gamma) h
  simp only [lessThanSpec,strictLess,equalEqn] at ds
  exact ⟨disjunctionElimination ds
    (Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (Derivation.explosion
      (sucNeZeroApply (Derivation.conjunctionRight
        (Derivation.hypothesis List.mem_cons_self)))))⟩

theorem notLessOfRejection (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (lessGraph z x y))) :
    Nonempty (Derivation body Gamma (ltF x y).not) := by
  obtain ⟨d⟩ := actualOriginalLessThanGraph body α z x y
  obtain ⟨h⟩ := h
  have ds := Derivation.implicationElimination
    (weakenClosed (Derivation.conjunctionLeft d) Gamma) h
  simp only [lessThanSpec,strictLess,equalEqn] at ds
  exact ⟨disjunctionElimination ds
    (Derivation.implicationIntroduction (Derivation.explosion
      (sucNeZeroApply (symm (Derivation.conjunctionRight
        (Derivation.hypothesis List.mem_cons_self))))))
    (Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.hypothesis List.mem_cons_self)))⟩

theorem actualOriginalLessThanAcceptance : InternalLessThanTargets.ActualOriginalLessThanAcceptance := by
  intro body α x y
  obtain ⟨hf⟩ := lessOfAcceptance (body := body) (Gamma := [lessGraph (suc z) x y]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := acceptOfLess (body := body) (Gamma := [ltF x y]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalLessThanRejection : InternalLessThanTargets.ActualOriginalLessThanRejection := by
  intro body α x y
  obtain ⟨hf⟩ := notLessOfRejection (body := body) (Gamma := [lessGraph z x y]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rejectOfNotLess (body := body) (Gamma := [(ltF x y).not]) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
