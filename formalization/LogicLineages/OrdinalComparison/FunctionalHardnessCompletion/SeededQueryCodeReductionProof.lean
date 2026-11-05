module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof
open OriginalDomain SourceClasses

private theorem fallback_unsatisfiable : ¬PolynomialSatisfiable fallbackSystem := by
  rintro ⟨p, hp⟩
  have h := hp .unit (by simp [fallbackSystem])
  have hz := congrArg (fun f : SourceFiniteExponentProjection.PolynomialGroup => f 0) h
  simpa [SourceFiniteExponentProjection.polynomialMeaning] using hz

private theorem system_properties (strict : Bool) (n : Nat) (s : System n) :
    (∀ τ ∈ (SeededSystem.compile s).context, τ.level ≤ 1) ∧
    InternalLevelBound 3 (sourcePair strict s).1 ∧
    InternalLevelBound 3 (sourcePair strict s).2 ∧
    (¬PolynomialSatisfiable s ↔ ∀ ρ : AdmissibleSubstitution (SeededSystem.compile s).context,
      GroundComparison strict (sourcePair strict s).1 (sourcePair strict s).2 ρ) := by
  have hb := SeededSystem.Proof.exactLevelThreeBounds n s
  have hs := SeededSystem.Proof.exactSingleQuerySemantics n s
  cases strict with
  | false => exact ⟨hb.1, hb.2.2.2.1, hb.2.2.2.2, hs.2.symm⟩
  | true => exact ⟨hb.1, hb.2.2.1, hb.2.1, hs.1.symm⟩

private theorem fallback_solution (strict : Bool) (e : Nat)
    (hbad : ¬encodedPolynomialSolvable e) (hcode : reduceCode strict e = fallbackCode strict) :
    ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      packGroundQuery a b = reduceCode strict e ∧ (∀ τ ∈ Γ, τ.level ≤ 1) ∧
      InternalLevelBound 3 a ∧ InternalLevelBound 3 b ∧
      (¬encodedPolynomialSolvable e ↔ ∀ ρ : AdmissibleSubstitution Γ, GroundComparison strict a b ρ) := by
  have hp := system_properties strict 0 fallbackSystem
  refine ⟨(SeededSystem.compile fallbackSystem).context,
    (sourcePair strict fallbackSystem).1, (sourcePair strict fallbackSystem).2,
    ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
  · rw [hcode]
    exact exactQueryCalibration strict 0 fallbackSystem
  · exact ⟨fun _ => hp.2.2.2.mp fallback_unsatisfiable, fun _ => hbad⟩

theorem exactTotalReduction : Targets.ExactTotalReduction := by
  intro strict e
  cases hdec : Encodable.decode (α := SystemCode) e with
  | none =>
      apply fallback_solution strict e
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
        have hp := system_properties strict c.1 (systemOfCode c)
        refine ⟨(SeededSystem.compile (systemOfCode c)).context,
          (sourcePair strict (systemOfCode c)).1, (sourcePair strict (systemOfCode c)).2,
          ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
        · rw [reduceCode, hdec]
          dsimp only
          rw [if_pos hw, (SeededInputCode.Proof.exactSystemInputs c).1]
          exact exactQueryCalibration strict c.1 (systemOfCode c)
        · exact (not_congr he).trans hp.2.2.2
      · apply fallback_solution strict e
        · rintro ⟨c', hc', hf, _⟩
          have hcc : c' = c := Option.some.inj (hc'.symm.trans hdec)
          subst c'
          exact hw ((exactWellFormed c).mpr hf)
        · simp only [reduceCode, hdec, if_neg hw]

theorem existingReductions : Targets.ExistingReductions := by
  constructor
  · exact ⟨reduceCode true, (reduce_pr.comp (Primrec.const true) Primrec.id).to_comp,
      exactTotalReduction true⟩
  · exact ⟨reduceCode false, (reduce_pr.comp (Primrec.const false) Primrec.id).to_comp,
      exactTotalReduction false⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof
