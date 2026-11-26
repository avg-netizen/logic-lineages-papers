module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeProgramsProof
public import LogicLineages.PermittedControl.StandardSeededSystemEmptyProof
public import LogicLineages.PermittedControl.StandardSingleQueryTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSingleQuery.Proof
open OrdinalComparison Source SourceClasses SelectedSourceDomain SelectedFiniteQuery
open Source.AdmissibleSum Source.FunctionalHardnessCompletion
open SeededQueryCode
open SeededQueryCode.Proof (exactQueryCalibration exactWellFormed reduce_pr)

private theorem fallback_unsatisfiable : ¬PolynomialSatisfiable fallbackSystem := by
  rintro ⟨p, hp⟩
  have h := hp .unit (by simp [fallbackSystem])
  have hz := congrArg (fun f : SourceFiniteExponentProjection.PolynomialGroup => f 0) h
  simpa [SourceFiniteExponentProjection.polynomialMeaning] using hz

private theorem system_properties (policy : Policy) (strict : Bool) (n : Nat) (s : System n) :
    (∀ τ ∈ (SeededSystem.compile s).context, τ.level ≤ 1) ∧
    InternalLevelBound 3 (sourcePair strict s).1 ∧
    InternalLevelBound 3 (sourcePair strict s).2 ∧
    (¬PolynomialSatisfiable s ↔ ∀ ρ : AdmissibleSubstitution Phi (SeededSystem.compile s).context,
      SelectedFiniteQuery.GroundComparison Phi policy strict (sourcePair strict s).1 (sourcePair strict s).2 ρ) := by
  have hb := StandardSeededSystem.Proof.levelThreeBounds n s
  have hs := StandardSeededSystem.Proof.queryComplements policy n s
  cases strict with
  | false => exact ⟨hb.1, hb.2.2.2.1, hb.2.2.2.2, hs.2.symm⟩
  | true => exact ⟨hb.1, hb.2.2.1, hb.2.1, hs.1.symm⟩

private theorem fallback_solution (policy : Policy) (strict : Bool) (e : Nat)
    (hbad : ¬encodedPolynomialSolvable e) (hcode : reduceCode strict e = fallbackCode strict) :
    ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      packGroundQuery a b = reduceCode strict e ∧ (∀ τ ∈ Γ, τ.level ≤ 1) ∧
      InternalLevelBound 3 a ∧ InternalLevelBound 3 b ∧
      (¬encodedPolynomialSolvable e ↔ ∀ ρ : AdmissibleSubstitution Phi Γ, SelectedFiniteQuery.GroundComparison Phi policy strict a b ρ) := by
  have hp := system_properties policy strict 0 fallbackSystem
  refine ⟨(SeededSystem.compile fallbackSystem).context,
    (sourcePair strict fallbackSystem).1, (sourcePair strict fallbackSystem).2,
    ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
  · rw [hcode]
    exact exactQueryCalibration strict 0 fallbackSystem
  · exact ⟨fun _ => hp.2.2.2.mp fallback_unsatisfiable, fun _ => hbad⟩

theorem exactTotalReduction : StandardSingleQuery.ExactTotalReduction := by
  intro policy strict e
  cases hdec : Encodable.decode (α := SystemCode) e with
  | none =>
      apply fallback_solution policy strict e
      · rintro ⟨c, hc, _, _⟩
        rw [hdec] at hc
        cases hc
      · simp only [reduceCode, hdec]
  | some c =>
      by_cases hw : validSystem c = true
      · have hf := (exactWellFormed c).mp hw
        have he : encodedPolynomialSolvable e ↔ PolynomialSatisfiable (systemOfCode c) := by
          constructor
          · rintro ⟨c', hc', _, hp⟩
            have hcc : c' = c := Option.some.inj (hc'.symm.trans hdec)
            subst c'
            exact hp
          · intro hp
            exact ⟨c, hdec, hf, hp⟩
        have hp := system_properties policy strict c.1 (systemOfCode c)
        refine ⟨(SeededSystem.compile (systemOfCode c)).context,
          (sourcePair strict (systemOfCode c)).1, (sourcePair strict (systemOfCode c)).2,
          ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
        · rw [reduceCode, hdec]
          dsimp only
          rw [if_pos hw, (SeededInputCode.Proof.exactSystemInputs c).1]
          exact exactQueryCalibration strict c.1 (systemOfCode c)
        · exact (not_congr he).trans hp.2.2.2
      · apply fallback_solution policy strict e
        · rintro ⟨c', hc', hf, _⟩
          have hcc : c' = c := Option.some.inj (hc'.symm.trans hdec)
          subst c'
          exact hw ((exactWellFormed c).mpr hf)
        · simp only [reduceCode, hdec, if_neg hw]

theorem bothReductions : StandardSingleQuery.BothReductions := by
  intro policy
  constructor
  · exact ⟨reduceCode true, (reduce_pr.comp (Primrec.const true) Primrec.id).to_comp,
      exactTotalReduction policy true⟩
  · exact ⟨reduceCode false, (reduce_pr.comp (Primrec.const false) Primrec.id).to_comp,
      exactTotalReduction policy false⟩

theorem standardSingleQuery : StandardSingleQuery.StandardSingleQuery :=
  ⟨SeededQueryCode.Proof.primitivePrograms, exactQueryCalibration, exactWellFormed,
    exactTotalReduction, bothReductions⟩
end LogicLineages.PermittedControl.StandardSingleQuery.Proof
