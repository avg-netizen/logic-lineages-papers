module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalEqualityTestCompositionProof InternalEqualityTestProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Original internal trichotomy supplies the rejecting value on every
unequal pair. This proof does not import native evaluation calibration. -/
theorem equalityReject (x y : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (eqn x y).not)) :
    Nonempty (Derivation body Gamma (equalityGraph z x y)) := by
  obtain ⟨hn⟩ := hn
  obtain ⟨cmp⟩ := actualOriginalComparison body alpha x y
  have hc := compareView (weakenClosed cmp Gamma)
  obtain ⟨hl⟩ := rejectForwardOrder (body := body) (Gamma := ltF x y :: Gamma) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Gamma) x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Derivation body (eqn x y :: Gamma) (equalityGraph z x y) :=
    Derivation.explosion (Derivation.implicationElimination (addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))
  have hrest : Derivation body Gamma
      ((eqn x y ⊔ ltF y x).imp (equalityGraph z x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

/-- Full graph, not just acceptance: exactly one on equal inputs and exactly
zero on unequal inputs, for arbitrary symbolic output. -/
theorem equalityEquation (out x y : OTerm alpha) :
    Nonempty (Derivation body [] ((equalityGraph out x y).iff (testSpec out x y))) := by
  have hy : Nonempty (Derivation body [] ((eqn x y).imp (equalityGraph (suc z) x y))) := by
    obtain ⟨h⟩ := equalityOfEqual (body := body) (Gamma := [eqn x y]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  have hn : Nonempty (Derivation body [] ((eqn x y).not.imp (equalityGraph z x y))) := by
    obtain ⟨h⟩ := equalityReject (body := body) (Gamma := [(eqn x y).not]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  simpa only [Formula.iff,BoundedFormula.iff,testSpec,equalEqn,equalityGraph] using
    (choiceEquation (body := body) InternalEqualityTest.equalityTest out (suc z) z
      (Fin.cons x (Fin.cons y Fin.elim0)) (eqn x y) hy hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
