module
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeTargets
public import LogicLineages.OrdinalComparison.WWCanonicalBoxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

theorem actualCanonicalPrimeEquations : Targets.ActualCanonicalPrimeEquations := by
  intro Γ
  refine ⟨fun _ _ => rfl, rfl, rfl, ?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · intro σ
    constructor
    · simp only [Ty.caseType, Ty.level]
      omega
    · rfl
  · intro σ
    constructor
    · simp only [Ty.recType, Ty.level]
      omega
    · rfl

theorem actualCanonicalPrimeGeneratedGrade : Targets.ActualCanonicalPrimeGeneratedGrade := by
  intro Γ τ t v h i
  cases t with
  | var x =>
    simp only [ordinalCanonicalPrime, Option.some.injEq] at h
    subst v
    exact .var x i
  | zeroC =>
    simp only [ordinalCanonicalPrime, Option.some.injEq] at h
    subst v
    exact .one i.val
  | succC =>
    simp only [ordinalCanonicalPrime, Option.some.injEq] at h
    subst v
    exact .one i.val
  | caseC σ =>
    simp only [ordinalCanonicalPrime, Option.some.injEq] at h
    subst v
    exact .one i.val
  | recC σ =>
    simp only [ordinalCanonicalPrime, Option.some.injEq] at h
    subst v
    dsimp only
    split
    · exact .add (.one i.val) (.one i.val)
    · rename_i hi
      split
      · exact .omega i.val (by omega)
      · exact .one i.val
  | app f g => simp [ordinalCanonicalPrime] at h
  | lam b => simp [ordinalCanonicalPrime] at h
  | ranked s args => nomatch s

theorem actualCanonicalTypedApplication : Targets.ActualCanonicalTypedApplication := by
  intro Γ σ τ
  have hσ : σ.level < (Ty.arrow σ τ).level :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  have hτ : τ.level ≤ (Ty.arrow σ τ).level := Nat.le_max_right _ _
  refine ⟨hσ, hτ, ?_⟩
  intro f g hf hg i
  have hi : i.val < (Ty.arrow σ τ).level + 1 :=
    Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hτ)
  constructor
  · exact actualCanonicalBoxGeneratedGrade Γ _ _ hσ f g hf hg ⟨i.val, hi⟩
  · simp [ordinalCanonicalApplication, ordinalVectorAt, hi]

end LogicLineages.OrdinalComparison.Source
