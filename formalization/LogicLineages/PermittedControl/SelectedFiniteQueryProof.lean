module
public import LogicLineages.PermittedControl.SelectedFiniteQueryTargets
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeCalibrationProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFiniteQuery.Proof
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum Source.SourceClasses
open Source.FunctionalHardnessCompletion
open Source.FunctionalHardnessCompletion.FiniteQueryCode

private theorem fallback_unsatisfiable : ¬PolynomialSatisfiable fallbackSystem := by
  rintro ⟨p, hp⟩
  have h := hp .unit (by simp [fallbackSystem])
  have hz := congrArg (fun f : SourceFiniteExponentProjection.PolynomialGroup => f 0) h
  simpa [SourceFiniteExponentProjection.polynomialMeaning] using hz

private theorem ground_query_bounds (strict : Bool) (n : Nat) (s : System n) :
    queryBounds 2 (groundQuery strict s) := by
  have hb := SelectedSystemReduction.Proof.levelTwoBounds n s
  cases strict with
  | false => exact ⟨hb.1, hb.2.2.2.1, hb.2.2.2.2⟩
  | true => exact ⟨hb.1, hb.2.2.1, hb.2.1⟩

private theorem queries_bounds (strict : Bool) (n : Nat) (s : System n) :
    ∀ q ∈ queries strict s, queryBounds 2 q := by
  intro q hq
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hq
  exact ground_query_bounds strict n (restrictSystem z s)

private theorem queries_semantics (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (policy : Policy) (strict : Bool) (n : Nat) (s : System n) :
    ¬PolynomialSatisfiable s ↔ ∀ q ∈ queries strict s, SelectedFiniteQuery.queryUniversal ctrl policy strict q := by
  simp only [queries, List.forall_mem_map]
  cases strict with
  | false => exact (SelectedPolynomialPatterns.Proof.allMaskQueries ctrl K hc policy n s).2
  | true => exact (SelectedPolynomialPatterns.Proof.allMaskQueries ctrl K hc policy n s).1

private theorem fallback_solution (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (policy : Policy) (strict : Bool) (e : Nat)
    (hbad : ¬encodedPolynomialSolvable e) (hcode : reduceCode strict e = fallbackCode strict) :
    ∃ qs : List GroundQuery, qs.map FunctionalHardnessCompletion.queryCode = reduceCode strict e ∧
      (∀ q ∈ qs, queryBounds 2 q) ∧
      (¬encodedPolynomialSolvable e ↔ ∀ q ∈ qs, SelectedFiniteQuery.queryUniversal ctrl policy strict q) := by
  refine ⟨queries strict fallbackSystem, ?_, queries_bounds strict 0 fallbackSystem, ?_⟩
  · rw [hcode]
    exact FiniteQueryCode.Proof.exactListCalibration strict 0 fallbackSystem
  · exact ⟨fun _ => (queries_semantics ctrl K hc policy strict 0 fallbackSystem).mp fallback_unsatisfiable,
      fun _ => hbad⟩

theorem exactTotalReduction : SelectedFiniteQueryTargets.ExactTotalReduction := by
  intro ctrl K hc policy strict e
  cases hdec : Encodable.decode (α := SystemCode) e with
  | none =>
      apply fallback_solution ctrl K hc policy strict e
      · rintro ⟨c, hc, _, _⟩
        rw [hdec] at hc
        cases hc
      · simp only [reduceCode, hdec]
  | some c =>
      by_cases hw : SeededQueryCode.validSystem c = true
      · have hf := (SeededQueryCode.Proof.exactWellFormed c).mp hw
        have he : encodedPolynomialSolvable e ↔ PolynomialSatisfiable (systemOfCode c) := by
          constructor
          · rintro ⟨c', hc', _, hp⟩
            have hcc : c' = c := Option.some.inj (hc'.symm.trans hdec)
            subst c'
            exact hp
          · intro hp
            exact ⟨c, hdec, hf, hp⟩
        refine ⟨queries strict (systemOfCode c), ?_, queries_bounds strict c.1 (systemOfCode c), ?_⟩
        · rw [reduceCode, hdec]
          dsimp only
          rw [if_pos hw, (SeededInputCode.Proof.exactSystemInputs c).1]
          exact FiniteQueryCode.Proof.exactListCalibration strict c.1 (systemOfCode c)
        · exact (not_congr he).trans (queries_semantics ctrl K hc policy strict c.1 (systemOfCode c))
      · apply fallback_solution ctrl K hc policy strict e
        · rintro ⟨c', hc', hf, _⟩
          have hcc : c' = c := Option.some.inj (hc'.symm.trans hdec)
          subst c'
          exact hw ((SeededQueryCode.Proof.exactWellFormed c).mpr hf)
        · simp only [reduceCode, hdec, if_neg hw]

theorem literalProgram : SelectedFiniteQueryTargets.LiteralProgram :=
  FiniteQueryCode.Proof.reduce_pr

theorem bothReductions : SelectedFiniteQueryTargets.BothReductions := by
  intro ctrl K hc policy
  constructor
  · exact ⟨reduceCode true,(FiniteQueryCode.Proof.reduce_pr.comp (Primrec.const true) Primrec.id).to_comp,
      exactTotalReduction ctrl K hc policy true⟩
  · exact ⟨reduceCode false,(FiniteQueryCode.Proof.reduce_pr.comp (Primrec.const false) Primrec.id).to_comp,
      exactTotalReduction ctrl K hc policy false⟩

theorem selectedFiniteQuery : SelectedFiniteQueryTargets.SelectedFiniteQuery :=
  ⟨literalProgram,exactTotalReduction,bothReductions⟩
end LogicLineages.PermittedControl.SelectedFiniteQuery.Proof
