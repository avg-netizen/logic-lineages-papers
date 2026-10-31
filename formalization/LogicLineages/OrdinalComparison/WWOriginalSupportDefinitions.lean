module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- A typed variable-vector name, not one particular ordinal coordinate. -/
abbrev VariableName (Γ : List Ty) := Σ τ : Ty, Variable Γ τ

def componentName {Γ : List Ty} (c : OrdinalComponent Γ) : VariableName Γ :=
  ⟨c.1, c.2.1⟩

def UsesOnly {Γ : List Ty} (S : VariableName Γ → Prop) (t : OrdinalExpression Γ) : Prop :=
  ∀ c ∈ ordinalExpressionVariables t, S (componentName c)

/-- Source Definition 2.7 includes the complete vector whenever any of its
coordinates occurs in either expression being compared. -/
def comparisonSupport {Γ : List Ty} (t u : OrdinalExpression Γ) (x : VariableName Γ) : Prop :=
  ∃ c, (c ∈ ordinalExpressionVariables t ∨ c ∈ ordinalExpressionVariables u) ∧ componentName c = x

structure SupportedSubstitution (Γ : List Ty) (S : VariableName Γ → Prop) where
  vector : {τ : Ty} → (x : Variable Γ τ) → S ⟨τ, x⟩ → Fin (τ.level + 1) → ClosedExpression
  graded : ∀ {τ : Ty} (x : Variable Γ τ) (hx : S ⟨τ, x⟩) (j : Fin (τ.level + 1)),
    ClosedGrade j.val (vector x hx j)
  bounded : ∀ {τ : Ty} (x : Variable Γ τ) (hx : S ⟨τ, x⟩) (j : Fin (τ.level + 1)),
    actualOrdinalNorm (closedValue (vector x hx j)) ≤
      actualOrdinalNorm (closedValue (vector x hx 0))

/-- Totalization by One only for names outside the source comparison support.
On a supported expression these values are unused; independence is proved
separately rather than postulated. -/
noncomputable def supportedValuation {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : SupportedSubstitution Γ S) (c : OrdinalComponent Γ) : Ordinal.{0} := by
  classical
  exact if hc : S (componentName c) then closedValue (ρ.vector c.2.1 hc c.2.2) else 1

noncomputable def supportedValue {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : SupportedSubstitution Γ S) (t : OrdinalExpression Γ) : Ordinal.{0} :=
  denote (supportedValuation ρ) t

end LogicLineages.OrdinalComparison.Source.OriginalDomain
