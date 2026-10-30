module

public import LogicLineages.OrdinalComparison.SourceApplicativeTargets
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceApplicativeProof
open Targets

theorem applicativeAssignmentEquations : ApplicativeAssignmentEquations := by
  refine ⟨?_, ?_, ?_⟩
  · intro Γ τ t v h
    cases t with
    | var x => exact h
    | zeroC => exact h
    | succC => exact h
    | caseC σ => exact h
    | recC σ => exact h
    | app f a => simp [ordinalCanonicalPrime] at h
    | lam body => simp [ordinalCanonicalPrime] at h
    | ranked s args => nomatch s
  · intro Γ σ τ f a; rfl
  · intro Γ σ τ body; rfl

theorem applicativeAssignmentDomain : ApplicativeAssignmentDomain := by
  intro Γ τ t
  induction t with
  | var x => simp [ordinalApplicativeAssignment, ordinalCanonicalPrime, applicativeOnly]
  | zeroC => simp [ordinalApplicativeAssignment, ordinalCanonicalPrime, applicativeOnly]
  | succC => simp [ordinalApplicativeAssignment, ordinalCanonicalPrime, applicativeOnly]
  | caseC σ => simp [ordinalApplicativeAssignment, ordinalCanonicalPrime, applicativeOnly]
  | recC σ => simp [ordinalApplicativeAssignment, ordinalCanonicalPrime, applicativeOnly]
  | lam body ih => simp [ordinalApplicativeAssignment, applicativeOnly]
  | ranked s args ih => nomatch s
  | app f a ihf iha =>
      simp only [applicativeOnly, Bool.and_eq_true, ← ihf, ← iha]
      cases hf : ordinalApplicativeAssignment f <;> cases ha : ordinalApplicativeAssignment a <;>
        simp [ordinalApplicativeAssignment, hf, ha]

theorem applicativeAssignmentGrade : ApplicativeAssignmentGrade := by
  intro Γ τ t
  induction t with
  | var x => intro v h; exact actualCanonicalPrimeGeneratedGrade _ _ _ _ h
  | zeroC => intro v h; exact actualCanonicalPrimeGeneratedGrade _ _ _ _ h
  | succC => intro v h; exact actualCanonicalPrimeGeneratedGrade _ _ _ _ h
  | caseC σ => intro v h; exact actualCanonicalPrimeGeneratedGrade _ _ _ _ h
  | recC σ => intro v h; exact actualCanonicalPrimeGeneratedGrade _ _ _ _ h
  | lam body ih => intro v h; simp [ordinalApplicativeAssignment] at h
  | ranked s args ih => nomatch s
  | @app Γ σ τ f a ihf iha =>
      intro v h
      change (ordinalApplicativeAssignment f).bind (fun vf =>
        (ordinalApplicativeAssignment a).bind (fun va => some (ordinalCanonicalApplication vf va))) = some v at h
      obtain ⟨vf, hf, va, ha, hv⟩ := (by
        simpa only [Option.bind_eq_some_iff, Option.some.injEq] using h)
      subst v
      intro i
      exact ((actualCanonicalTypedApplication Γ σ τ).2.2 vf va (ihf vf hf) (iha va ha) i).1

theorem successorProbeAssignment : SuccessorProbeAssignment := by
  intro Γ v
  simp only [successorProbe, ordinalApplicativeAssignment, ordinalCanonicalPrime, Option.bind_some]
  change some (ordinalCanonicalApplication (σ := .ground) (τ := .ground)
    (fun _ => .one) (fun i => .var ⟨.ground, v, i⟩)) = _
  apply congrArg Option.some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [ordinalCanonicalApplication, ordinalCanonicalBox, ordinalBoxPositive,
    ordinalVectorAt, ordinalBoxScalarTail, Ty.level]

end LogicLineages.OrdinalComparison.Source.SourceApplicativeProof
