module
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def ActualCanonicalPrimeEquations : Prop :=
  ∀ Γ : List Ty,
    (∀ (σ : Ty) (v : Variable Γ σ), ordinalCanonicalPrime (.var v) =
      some (fun i => .var ⟨σ, v, i⟩)) ∧
    (ordinalCanonicalPrime (Γ := Γ) .zeroC = some (fun _ => .one)) ∧
    (ordinalCanonicalPrime (Γ := Γ) .succC = some (fun _ => .one)) ∧
    (∀ σ : Ty, σ.caseType.level = σ.level + 1 ∧
      ordinalCanonicalPrime (Γ := Γ) (.caseC σ) = some (fun _ => .one)) ∧
    (∀ σ : Ty, σ.recType.level = σ.level + 2 ∧
      ordinalCanonicalPrime (Γ := Γ) (.recC σ) = some (fun i =>
        if i.val = 0 then .add .one .one else if i.val = σ.level + 2 then .omega else .one)) ∧
    (∀ (σ τ : Ty) (f : OriginalTerm Γ (.arrow σ τ)) (g : OriginalTerm Γ σ),
      ordinalCanonicalPrime (.app f g) = none) ∧
    (∀ (σ τ : Ty) (b : OriginalTerm (σ :: Γ) τ), ordinalCanonicalPrime (.lam b) = none)

def ActualCanonicalPrimeGeneratedGrade : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ) (v : OrdinalVector Γ τ.level),
    ordinalCanonicalPrime t = some v → ∀ i, GeneratedOrdinalGrade Γ i.val (v i)

def ActualCanonicalTypedApplication : Prop :=
  ∀ (Γ : List Ty) (σ τ : Ty),
    σ.level < (Ty.arrow σ τ).level ∧ τ.level ≤ (Ty.arrow σ τ).level ∧
    ∀ (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level),
      (∀ i, GeneratedOrdinalGrade Γ i.val (f i)) →
      (∀ i, GeneratedOrdinalGrade Γ i.val (g i)) →
      ∀ i, GeneratedOrdinalGrade Γ i.val (ordinalCanonicalApplication f g i) ∧
        ordinalCanonicalApplication f g i =
          ordinalVectorAt (ordinalCanonicalBox f g) i.val

end LogicLineages.OrdinalComparison.Source.Targets
