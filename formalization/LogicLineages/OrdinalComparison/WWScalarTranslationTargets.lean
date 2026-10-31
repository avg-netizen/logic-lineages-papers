module
public import LogicLineages.OrdinalComparison.WWScalarTranslationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Exact shared-valuation equality, even for natural-valued inputs including
zero. In particular this preserves every positive source input valuation,
without independent copies for repeated variables or introduced parameters. -/
def ScalarTranslationSound : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (s : Scalar (OrdinalComponent Γ)),
    compileScalar t = some s → ∀ ρ : OrdinalComponent Γ → Nat,
      (s.value ρ : Ordinal) = denote (fun c => (ρ c : Ordinal)) t

/-- Every generated scalar over an all-ground free context is compiled.
Arbitrary internal types/binders/recursors were handled by the independently
proved assignment-generation theorem; no restriction on them is added here. -/
def GeneratedGroundScalarTranslationTotal : Prop :=
  ∀ (Γ : List Ty), (∀ τ ∈ Γ, τ = Ty.ground) →
    ∀ t : OrdinalExpression Γ, GeneratedOrdinalGrade Γ 0 t →
      ∃ s : Scalar (OrdinalComponent Γ), compileScalar t = some s

end LogicLineages.OrdinalComparison.Source.Targets
