module
public import LogicLineages.PermittedControl.SelectedSourceSupportDefinitions
public import LogicLineages.PermittedControl.LiteralCovarianceDefinitions
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedWeakScalarTargets
open OrdinalComparison Source SelectedSourceDomain SelectedSourceSupport Source.AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual interpretation depends only on the literal occurring components. -/
def EvaluationIndependence : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty)
    (t : OrdinalExpression Γ) (ρ τ : OrdinalComponent Γ → Ordinal.{0}),
    (∀ c ∈ ordinalExpressionVariables t, ρ c = τ c) →
    ParametricSourceSuccessor.denoteWith ctrl ρ t = ParametricSourceSuccessor.denoteWith ctrl τ t

def SupportedExtension : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty)
    (S : VariableName Γ → Prop) (ρ : SupportedSubstitution ctrl Γ S),
    ∃ ρ' : AdmissibleSubstitution ctrl Γ, ∀ c, valuation ctrl ρ' c = supportedValuation ctrl ρ c

def ComparisonSupportCoverage : Prop := ∀ (Γ : List Ty) (t u : OrdinalExpression Γ),
    UsesOnly (comparisonSupport t u) t ∧ UsesOnly (comparisonSupport t u) u

def SupportComparisonBridge : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty)
    (S : VariableName Γ → Prop) (t u : OrdinalExpression Γ),
    UsesOnly S t → UsesOnly S u → ∀ P : Ordinal.{0} → Ordinal.{0} → Prop,
    (∀ ρ : AdmissibleSubstitution ctrl Γ, P (expressionValue ctrl ρ t) (expressionValue ctrl ρ u)) ↔
    (∀ ρ : SupportedSubstitution ctrl Γ S, P (supportedValue ctrl ρ t) (supportedValue ctrl ρ u))

/-- Genuine simultaneous partial success, grade and weak scalar inequality. -/
def PartialWeakAndValid : Prop := ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade ctrl Γ σ i t → ∃ v : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run p i t = some v ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧
      (i = 0 → ∀ ρ : AdmissibleSubstitution ctrl Γ,
        expressionValue ctrl ρ (ordinalHeadClosure t) ≤ expressionValue ctrl ρ (v 0))

/-- All three printed clauses, using exactly occurring whole-vector substitutions. -/
def SourceWeakScalar : Prop := ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy),
    (∀ t : OrdinalExpression (σ :: Γ), HeadGrade ctrl Γ σ 0 t →
      ∃ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p 0 t = some v ∧
        ∀ ρ : SupportedSubstitution ctrl Γ (comparisonSupport (ordinalHeadClosure t) (v 0)),
          supportedValue ctrl ρ (ordinalHeadClosure t) ≤ supportedValue ctrl ρ (v 0)) ∧
    (∀ (i : Nat) (t : OrdinalExpression (σ :: Γ)), HeadGrade ctrl Γ σ i t →
      ∃ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p i t = some v ∧
        ∀ j, AmbientGrade ctrl Γ j.val (v j) ∧
          ordinalHeadFree (σ := σ) (LiteralCovariance.weaken σ (v j)) = true) ∧
    (∀ (m : Nat) (h : OrdinalVector (σ :: Γ) m),
      (∀ i, HeadGrade ctrl Γ σ i.val (h i)) →
      ∃ v : OrdinalVector Γ (max (σ.level + 1) m), LiteralCovariance.delta p h = some v ∧
        ∀ j, AmbientGrade ctrl Γ j.val (v j) ∧
          ordinalHeadFree (σ := σ) (LiteralCovariance.weaken σ (v j)) = true)

def FullSelectedWeakScalar : Prop := EvaluationIndependence ∧ SupportedExtension ∧
  ComparisonSupportCoverage ∧ SupportComparisonBridge ∧ PartialWeakAndValid ∧ SourceWeakScalar

end LogicLineages.PermittedControl.SelectedWeakScalarTargets
