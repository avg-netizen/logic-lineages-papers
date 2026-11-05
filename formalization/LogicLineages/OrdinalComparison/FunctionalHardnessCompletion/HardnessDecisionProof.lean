module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionFoldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Proof

theorem conjunctionMeaning : Targets.ConjunctionMeaning := by
  intro answer queries
  induction queries with
  | nil => simp [allAnswers]
  | cons q qs ih =>
    simp only [allAnswers,List.foldr_cons,Bool.and_eq_true,List.forall_mem_cons] at *
    exact and_congr Iff.rfl ih

/-- The number of source queries may depend on the system input. Ordinary
computable recursion over that actual finite list preserves totality. -/
theorem conjunctionComputable : Targets.ConjunctionComputable := by
  intro answer hanswer
  have hstep : Computable₂ (fun _ : List Nat => fun item : Nat × Bool =>
      answer item.1 && item.2) :=
    (Primrec.and.to_comp.comp
      (hanswer.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  exact FoldProof.computable_foldr 0 Computable.id (Computable.const true) hstep

/-- Only well-formed bounded queries supplied by the exact reduction are
submitted to the hypothetical algorithm. Malformed query answers are unused. -/
theorem finiteQueryPullback : Targets.FiniteQueryPullback := by
  intro strict hreduce hdecider
  obtain ⟨reduce,hcompute,hreduce⟩ := hreduce
  obtain ⟨answer,hanswer,hcorrect⟩ := hdecider
  have hbool : Computable (fun e => allAnswers answer (reduce e)) :=
    (conjunctionComputable answer hanswer).comp hcompute
  have hmeaning : ∀ e,
      ¬encodedPolynomialSolvable e ↔ allAnswers answer (reduce e)=true := by
    intro e
    obtain ⟨queries,hcodes,hbounds,hsem⟩ := hreduce e
    have hanswerCorrect : ∀ q∈queries,
        answer (queryCode q)=true ↔ queryUniversal strict q := by
      intro q hq
      rcases q with ⟨Γ,a,b⟩
      have hb := hbounds ⟨Γ,a,b⟩ hq
      exact hcorrect Γ a b hb.1 hb.2.1 hb.2.2
    rw [←hcodes,conjunctionMeaning answer (queries.map queryCode)]
    simp only [List.forall_mem_map]
    constructor
    · intro hs q hq
      exact (hanswerCorrect q hq).mpr (hsem.mp hs q hq)
    · intro hs
      apply hsem.mpr
      intro q hq
      exact (hanswerCorrect q hq).mp (hs q hq)
  have hcomplement : ComputablePred (fun e => ¬encodedPolynomialSolvable e) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨(fun e => allAnswers answer (reduce e)),hbool,?_⟩
    exact funext (fun e => propext (hmeaning e))
  exact hcomplement.not.of_eq (fun e => by simp)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Proof
