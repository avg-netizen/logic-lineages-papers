module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource

theorem exists_reconstruct (p : SourceFormula) :
    SourceParameterDecision.existsBind (peelExists p).1 (peelExists p).2 = p := by
  induction p with
  | equal a b => rfl
  | less a b => rfl
  | negative p ih => rfl
  | conjunction p q ihp ihq => rfl
  | existsNat i p ih =>
      change SourceFormula.existsNat i
        (SourceParameterDecision.existsBind (peelExists p).1 (peelExists p).2) = .existsNat i p
      rw [ih]

theorem forall_reconstruct (p : SourceFormula) :
    SourceParameterDecision.forallBind (peelForall p).1 (peelForall p).2 = p := by
  cases p with
  | equal a b => rfl
  | less a b => rfl
  | conjunction p q => rfl
  | existsNat i p => rfl
  | negative q =>
      cases q with
      | equal a b => rfl
      | less a b => rfl
      | negative p => rfl
      | conjunction p q => rfl
      | existsNat i r =>
          cases r with
          | equal a b => rfl
          | less a b => rfl
          | conjunction p q => rfl
          | existsNat j p => rfl
          | negative p =>
              have h := forall_reconstruct p
              change SourceFormula.negative (.existsNat i (.negative
                (SourceParameterDecision.forallBind (peelForall p).1 (peelForall p).2))) =
                  .negative (.existsNat i (.negative p))
              rw [h]
termination_by sizeOf p

theorem literalReconstruction : HomogeneousSourceTargets.LiteralReconstruction :=
  fun p => ⟨exists_reconstruct p, forall_reconstruct p⟩

theorem exactDecisionDomain : HomogeneousSourceTargets.ExactDecisionDomain := by
  intro values p
  unfold HomogeneousSource.decide
  dsimp only
  by_cases he : SourceBooleanGraph.test (peelExists p).2 = true
  · rw [if_pos he, (SourceParameterDecisionProof.exactDecisionDomain (peelExists p).1 values (peelExists p).2).1]
    simp [admissible, he]
  · rw [if_neg he]
    rw [(SourceParameterDecisionProof.exactDecisionDomain (peelForall p).1 values (peelForall p).2).2]
    simp [admissible, Bool.eq_false_iff.mpr he]

theorem actualDecision : HomogeneousSourceTargets.ActualDecision := by
  intro values p hp b
  unfold HomogeneousSource.decide
  dsimp only
  by_cases he : SourceBooleanGraph.test (peelExists p).2 = true
  · rw [if_pos he]
    have h := (SourceParameterDecisionProof.actualSourceDecisions
      (peelExists p).1 values (peelExists p).2 he b).1
    rw [exists_reconstruct] at h
    exact h
  · rw [if_neg he]
    have ha : SourceBooleanGraph.test (peelForall p).2 = true := by
      rcases Bool.or_eq_true_iff.mp hp with h | h
      · exact False.elim (he h)
      · exact h
    have h := (SourceParameterDecisionProof.actualSourceDecisions
      (peelForall p).1 values (peelForall p).2 ha b).2
    rw [forall_reconstruct] at h
    exact h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
