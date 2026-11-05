module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceProof
open CommonLayerSyntax FiniteSearchSource

theorem test_eq (p : SourceFormula) : test p = (ScopedPhiParameters.test [] p || match p with
    | .negative q => test q
    | .conjunction q r => test q && test r
    | .existsNat i q => (BoundedSource.guard i q).isSome && test q
    | _ => false) := by cases p <;> rfl

theorem answer_eq (values : List Nat) (p : SourceFormula) : answer values p =
    (if ScopedPhiParameters.test [] p then (ScopedPhiParameters.decide values p).getD false
      else match p with
      | .negative q => !answer values q
      | .conjunction q r => answer values q && answer values r
      | .existsNat i q => match BoundedSource.guard i q with
          | none => false
          | some t => (List.range (t.value (PlainParameterDecision.valuation values))).any (fun n =>
              answer (BoundedSourcePrograms.Code.update values i n) q)
      | _ => false) := by cases p <;> rfl

theorem freeTerm (t : BaseTerm) : ScopedPhiParameters.termTest [] t = true := by
  induction t <;> simp_all [ScopedPhiParameters.termTest]

theorem scoped_inclusion (p : SourceFormula) (hp : ScopedPhiParameters.test [] p = true) : test p = true := by
  rw [test_eq, hp]; rfl

theorem supplierInclusion : FiniteSearchSourceTargets.SupplierInclusion := by
  refine ⟨scoped_inclusion, ?_⟩
  intro p
  induction p with
  | equal a b => intro _; apply scoped_inclusion; simp [ScopedPhiParameters.test, freeTerm]
  | less a b => intro _; apply scoped_inclusion; simp [ScopedPhiParameters.test, freeTerm]
  | negative p ih =>
      intro hp
      rw [test_eq]
      simp [ih hp]
  | conjunction p q ihp ihq =>
      intro hp
      have hh := Bool.and_eq_true_iff.mp hp
      rw [test_eq]
      simp [ihp hh.1, ihq hh.2]
  | existsNat i p ih =>
      intro hp
      have hh := Bool.and_eq_true_iff.mp hp
      rw [test_eq]
      simp [hh.1, ih hh.2]

theorem scoped_truth (values : List Nat) (p : SourceFormula) (hp : ScopedPhiParameters.test [] p = true) :
    answer values p = true ↔ p.eval (PlainParameterDecision.valuation values) := by
  rw [answer_eq, if_pos hp]
  have ht := ScopedPhiParametersProof.actualDecision values p hp true
  cases ha : ScopedPhiParameters.decide values p <;> simp_all

theorem actualTruth : FiniteSearchSourceTargets.ActualTruth := by
  intro values p
  induction p generalizing values with
  | equal a b =>
      intro _; apply scoped_truth; simp [ScopedPhiParameters.test, freeTerm]
  | less a b =>
      intro _; apply scoped_truth; simp [ScopedPhiParameters.test, freeTerm]
  | negative p ih =>
      intro hp
      by_cases hs : ScopedPhiParameters.test [] (.negative p) = true
      · exact scoped_truth values _ hs
      · rw [test_eq, Bool.eq_false_iff.mpr hs] at hp
        have ht := ih values hp
        rw [answer_eq, if_neg hs]
        cases ha : answer values p <;> simp_all [SourceFormula.eval]
  | conjunction p q ihp ihq =>
      intro hp
      by_cases hs : ScopedPhiParameters.test [] (.conjunction p q) = true
      · exact scoped_truth values _ hs
      · rw [test_eq, Bool.eq_false_iff.mpr hs] at hp
        have hh := Bool.and_eq_true_iff.mp hp
        rw [answer_eq, if_neg hs]
        simpa only [Bool.and_eq_true, SourceFormula.eval] using and_congr (ihp values hh.1) (ihq values hh.2)
  | existsNat i p ih =>
      intro hp
      by_cases hs : ScopedPhiParameters.test [] (.existsNat i p) = true
      · exact scoped_truth values _ hs
      · rw [test_eq, Bool.eq_false_iff.mpr hs] at hp
        have hh := Bool.and_eq_true_iff.mp hp
        rw [answer_eq, if_neg hs]
        have hu : ∀ n, PlainParameterDecision.valuation (BoundedSourcePrograms.Code.update values i n) =
            Function.update (PlainParameterDecision.valuation values) i n := by
          intro n; funext j; exact BoundedSourceProgramsProof.exactFiniteUpdate values i n j
        cases hg : BoundedSource.guard i p with
        | none => simp [hg] at hh
        | some t =>
            simp only [hg, List.any_eq_true, List.mem_range]
            change (∃ n < t.value (PlainParameterDecision.valuation values),
                answer (BoundedSourcePrograms.Code.update values i n) p = true) ↔
              ∃ n, p.eval (Function.update (PlainParameterDecision.valuation values) i n)
            constructor
            · rintro ⟨n, _, hn⟩
              have he := (ih _ hh.2).mp hn
              rw [hu] at he
              exact ⟨n, he⟩
            · rintro ⟨n, hn⟩
              refine ⟨n, (BoundedSourceProof.exactGuardInvariance i p t hg _ n).2 hn, ?_⟩
              apply (ih _ hh.2).mpr
              rwa [hu]

theorem actualDecision : FiniteSearchSourceTargets.ActualDecision := by
  intro values p
  constructor
  · by_cases hp : test p = true
    · simp [FiniteSearchSource.decide, hp]
    · simp [FiniteSearchSource.decide, hp, Bool.eq_false_iff.mpr hp]
  · intro hp b
    rw [FiniteSearchSource.decide, if_pos hp]
    have ht := actualTruth values p hp
    cases ha : answer values p <;> cases b <;> simp_all

theorem activeEnvironmentSearch : FiniteSearchSourceTargets.ActiveEnvironmentSearch := by
  intro values i p t hs hg
  rw [answer_eq]
  simp [hs, hg]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceProof
