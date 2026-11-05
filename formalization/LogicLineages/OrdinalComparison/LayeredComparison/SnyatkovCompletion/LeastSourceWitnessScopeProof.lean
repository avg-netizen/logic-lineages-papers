module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
open CommonLayerSyntax LeastSourceWitness

theorem term_mono (small large : List Nat) (t : BaseTerm) (hsub : ∀ i ∈ small, i ∈ large)
    (ht : ScopedPhiParameters.termTest large t = true) : ScopedPhiParameters.termTest small t = true := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b iha ihb =>
      have hh := Bool.and_eq_true_iff.mp ht
      exact Bool.and_eq_true_iff.mpr ⟨iha hh.1, ihb hh.2⟩
  | phi t ih =>
      rw [ScopedPhiParametersProof.phi_test] at ht ⊢
      intro i hi his
      exact ht i hi (hsub i his)

theorem formula_mono (small large : List Nat) (p : SourceFormula) (hsub : ∀ i ∈ small, i ∈ large)
    (hp : ScopedPhiParameters.test large p = true) : ScopedPhiParameters.test small p = true := by
  induction p generalizing small large with
  | equal a b =>
      have hh := Bool.and_eq_true_iff.mp hp
      exact Bool.and_eq_true_iff.mpr ⟨term_mono small large a hsub hh.1, term_mono small large b hsub hh.2⟩
  | less a b =>
      have hh := Bool.and_eq_true_iff.mp hp
      exact Bool.and_eq_true_iff.mpr ⟨term_mono small large a hsub hh.1, term_mono small large b hsub hh.2⟩
  | negative p ih => exact ih small large hsub hp
  | conjunction p q ihp ihq =>
      have hh := Bool.and_eq_true_iff.mp hp
      exact Bool.and_eq_true_iff.mpr ⟨ihp small large hsub hh.1, ihq small large hsub hh.2⟩
  | existsNat i p ih =>
      apply ih (i :: small) (i :: large) _ hp
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub j hj)

theorem scopeMonotonicity : LeastSourceWitnessTargets.ScopeMonotonicity := ⟨term_mono, formula_mono⟩

theorem existentialBodyAdmission : LeastSourceWitnessTargets.ExistentialBodyAdmission := by
  intro i p hp
  rw [FiniteSearchSourceProof.test_eq] at hp
  rcases Bool.or_eq_true_iff.mp hp with hs | hb
  · apply FiniteSearchSourceProof.scoped_inclusion
    exact formula_mono [] [i] p (by simp) hs
  · exact (Bool.and_eq_true_iff.mp hb).2

theorem need_true_iff (values : List Nat) (i : Nat) (p : SourceFormula)
    (hp : FiniteSearchSource.test (.existsNat i p) = true) :
    need (values, i, p.encode) = true ↔ (SourceFormula.existsNat i p).eval (PlainParameterDecision.valuation values) := by
  change decide (FiniteSearchPrograms.Code.decide values (SourceFormula.existsNat i p).encode = some true) = true ↔ _
  rw [decide_eq_true_eq, FiniteSearchProgramsProof.literalDecisionCode values (.existsNat i p)]
  simpa using (FiniteSearchSourceProof.actualDecision values (.existsNat i p)).2 hp true

theorem need_admission (values : List Nat) (i : Nat) (p : SourceFormula)
    (hn : need (values, i, p.encode) = true) : FiniteSearchSource.test (.existsNat i p) = true := by
  have hd : FiniteSearchPrograms.Code.decide values (SourceFormula.existsNat i p).encode = some true := by
    simpa [need, parent, SourceFormula.encode] using hn
  rw [FiniteSearchProgramsProof.literalDecisionCode values (.existsNat i p)] at hd
  by_cases hp : FiniteSearchSource.test (.existsNat i p) = true
  · exact hp
  · simp [FiniteSearchSource.decide, hp] at hd

theorem body_truth (values : List Nat) (i : Nat) (p : SourceFormula)
    (hp : FiniteSearchSource.test (.existsNat i p) = true) (n : Nat) :
    FiniteSearchPrograms.Code.answer (BoundedSourcePrograms.Code.update values i n) p.encode = true ↔
      p.eval (Function.update (PlainParameterDecision.valuation values) i n) := by
  rw [FiniteSearchProgramsProof.literalAnswerCode]
  have hval : PlainParameterDecision.valuation (BoundedSourcePrograms.Code.update values i n) =
      Function.update (PlainParameterDecision.valuation values) i n := by
    funext j; exact BoundedSourceProgramsProof.exactFiniteUpdate values i n j
  rw [FiniteSearchSourceProof.actualTruth _ p (existentialBodyAdmission i p hp), hval]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProof
