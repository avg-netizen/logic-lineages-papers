module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge
open InternalControlGraphSupportProof InternalControlGraphValueProof InternalControlGraphChoiceProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem zeroTestAtZero (t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t z))) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest (suc z) (Fin.cons t Fin.elim0))) := by
  obtain ⟨h⟩ := h
  exact headTransport _ (suc z) z t Fin.elim0 ⟨symm h⟩ zeroTestZeroValue

theorem zeroTestAtNonzero (t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t z).not)) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowPRInternalControl.zeroTest z (Fin.cons t Fin.elim0))) := by
  apply nonzeroValue _ z t Fin.elim0 h
  intro β j Delta v
  simp only [zRelabel,emptyRename]
  exact zeroTestSuccessorValue v

theorem conditionalAtZero (t a b : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t z))) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional a
      (Fin.cons t (Fin.cons a (Fin.cons b Fin.elim0))))) := by
  obtain ⟨h⟩ := h
  exact headTransport _ a z t (Fin.cons a (Fin.cons b Fin.elim0))
    ⟨symm h⟩ (conditionalZeroValue a b)

theorem conditionalAtNonzero (t a b : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t z).not)) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional b
      (Fin.cons t (Fin.cons a (Fin.cons b Fin.elim0))))) := by
  apply nonzeroValue _ b t (Fin.cons a (Fin.cons b Fin.elim0)) h
  intro β j Delta v
  simp only [consTermRename,emptyRename]
  exact conditionalSuccessorValue v (a.relabel j) (b.relabel j)

theorem equalsOneAtOne (t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t (suc z)))) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowVerifierNormalization.equalsOne (suc z) (Fin.cons t Fin.elim0))) := by
  obtain ⟨h⟩ := h
  exact headTransport _ (suc z) (suc z) t Fin.elim0 ⟨symm h⟩ equalsOneOneValue

/-- Non-one control is split internally at zero and successor. Successor
congruence turns a zero predecessor into the forbidden input ONE. -/
theorem equalsOneAtNonone (t : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn t (suc z)).not)) :
    Nonempty (Derivation body Gamma
      (programGraph GorbowVerifierNormalization.equalsOne z (Fin.cons t Fin.elim0))) := by
  apply zeroSuccessorCases Gamma t _
  · exact headTransport _ z z t Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ equalsOneZeroValue
  · intro β j Delta v hj ⟨he⟩
    simp only [programRename,consTermRename,emptyRename,zRelabel]
    have hn := renameInto h j Delta hj
    change Nonempty (Derivation body Delta (((eqn t (suc z)).relabel j).not)) at hn
    rw [eqnRelabel,sucRelabel,zRelabel] at hn
    obtain ⟨hn⟩ := hn
    have hzero : Nonempty (Derivation body Delta (eqn v z).not) := by
      apply Nonempty.intro
      apply Derivation.implicationIntroduction
      exact Derivation.implicationElimination (addHyp hn _)
        (trans (addHyp he _) (congSuc (Derivation.hypothesis List.mem_cons_self)))
    have step := equalsOneSuccessorValue z v (zeroTestAtNonzero v hzero)
    exact headTransport _ z (suc v) (t.relabel j) Fin.elim0 ⟨symm he⟩ step

theorem actualOriginalZeroTestGraph : InternalControlGraphTargets.ActualOriginalZeroTestGraph := by
  intro body α out input
  have hy : Nonempty (Derivation body [] ((eqn input z).imp
      (programGraph GorbowPRInternalControl.zeroTest (suc z) (Fin.cons input Fin.elim0)))) := by
    obtain ⟨d⟩ := zeroTestAtZero (body := body) (Gamma := [eqn input z]) input
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hn : Nonempty (Derivation body [] ((eqn input z).not.imp
      (programGraph GorbowPRInternalControl.zeroTest z (Fin.cons input Fin.elim0)))) := by
    obtain ⟨d⟩ := zeroTestAtNonzero (body := body) (Gamma := [(eqn input z).not]) input
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  simpa only [testSpec,equalEqn] using
    (choiceEquation GorbowPRInternalControl.zeroTest out (suc z) z
      (Fin.cons input Fin.elim0) (eqn input z) hy hn)

theorem actualOriginalConditionalGraph : InternalControlGraphTargets.ActualOriginalConditionalGraph := by
  intro body α out control a b
  have hy : Nonempty (Derivation body [] ((eqn control z).imp
      (programGraph GorbowPRInternalControl.conditional a
        (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0)))))) := by
    obtain ⟨d⟩ := conditionalAtZero (body := body) (Gamma := [eqn control z]) control a b
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hn : Nonempty (Derivation body [] ((eqn control z).not.imp
      (programGraph GorbowPRInternalControl.conditional b
        (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0)))))) := by
    obtain ⟨d⟩ := conditionalAtNonzero (body := body) (Gamma := [(eqn control z).not]) control a b
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  simpa only [conditionalSpec,equalEqn] using
    (choiceEquation GorbowPRInternalControl.conditional out a b
      (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) (eqn control z) hy hn)

theorem actualOriginalEqualsOneGraph : InternalControlGraphTargets.ActualOriginalEqualsOneGraph := by
  intro body α out input
  have hy : Nonempty (Derivation body [] ((eqn input (suc z)).imp
      (programGraph GorbowVerifierNormalization.equalsOne (suc z) (Fin.cons input Fin.elim0)))) := by
    obtain ⟨d⟩ := equalsOneAtOne (body := body) (Gamma := [eqn input (suc z)]) input
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hn : Nonempty (Derivation body [] ((eqn input (suc z)).not.imp
      (programGraph GorbowVerifierNormalization.equalsOne z (Fin.cons input Fin.elim0)))) := by
    obtain ⟨d⟩ := equalsOneAtNonone (body := body) (Gamma := [(eqn input (suc z)).not]) input
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  simpa only [testSpec,equalEqn] using
    (choiceEquation GorbowVerifierNormalization.equalsOne out (suc z) z
      (Fin.cons input Fin.elim0) (eqn input (suc z)) hy hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphProof
