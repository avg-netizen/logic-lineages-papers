module
public import LogicLineages.PermittedControl.SelectedSourceDomainDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSourceSupport
open OrdinalComparison Source SelectedSourceDomain
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

structure SupportedSubstitution (ctrl : Nat → Nat) (Γ : List Ty) (S : VariableName Γ → Prop) where
  vector : {τ : Ty} → (x : Variable Γ τ) → S ⟨τ, x⟩ → Fin (τ.level + 1) → ClosedExpression
  graded : ∀ {τ : Ty} (x : Variable Γ τ) (hx : S ⟨τ, x⟩) (j : Fin (τ.level + 1)),
    ClosedGrade ctrl j.val (vector x hx j)
  bounded : ∀ {τ : Ty} (x : Variable Γ τ) (hx : S ⟨τ, x⟩) (j : Fin (τ.level + 1)),
    actualOrdinalNorm (closedValue ctrl (vector x hx j)) ≤
      actualOrdinalNorm (closedValue ctrl (vector x hx 0))

/-- Totalization by One only for names outside the source comparison support.
On a supported expression these values are unused; independence is proved
separately rather than postulated. -/
noncomputable def supportedValuation (ctrl : Nat → Nat) {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : SupportedSubstitution ctrl Γ S) (c : OrdinalComponent Γ) : Ordinal.{0} := by
  classical
  exact if hc : S (componentName c) then closedValue ctrl (ρ.vector c.2.1 hc c.2.2) else 1

noncomputable def supportedValue (ctrl : Nat → Nat) {Γ : List Ty} {S : VariableName Γ → Prop}
    (ρ : SupportedSubstitution ctrl Γ S) (t : OrdinalExpression Γ) : Ordinal.{0} :=
  ParametricSourceSuccessor.denoteWith ctrl (supportedValuation ctrl ρ) t

end LogicLineages.PermittedControl.SelectedSourceSupport
