module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LiteralPolicy

/-- Syntactic generated-grade preservation for L and R. This intentionally is
not the larger original admissibility class with its collapse norm premise. -/
def ActualPolicyGeneratedPartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (policy : ActiveSumAssociation)
    (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t →
    ∃ v, policyPartial policy i t = some v ∧
      ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

def ActualPolicyGeneratedAbstraction : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (policy : ActiveSumAssociation)
    (h : OrdinalVector (σ :: Γ) m),
    (∀ i, GeneratedOrdinalGrade (σ :: Γ) i.val (h i)) →
    ∃ v, abstraction policy h = some v ∧
      ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

/-- Totality and exact generated syntax of the literal zero-history assignment
on the actual original-T kernel, including arbitrary binders and recursors. -/
def ActualPolicyGeneratedAssignment : Prop :=
  ∀ (Γ : List Ty) (τ : Ty) (policy : ActiveSumAssociation)
    (t : OriginalTerm Γ τ),
    ∃ v, assignment policy t = some v ∧
      ∀ j, GeneratedOrdinalGrade Γ j.val (v j)

/-- The positive-coordinate closedness part of the repaired forward theorem,
for the two fixed policies and all original typed sources with ground context.
No computable evaluator or scalar translation is smuggled into this target. -/
def ActualPolicyGroundPositiveClosed : Prop :=
  ∀ (Γ : List Ty), (∀ τ ∈ Γ, τ = Ty.ground) →
    ∀ (τ : Ty) (policy : ActiveSumAssociation) (t : OriginalTerm Γ τ),
    ∃ v, assignment policy t = some v ∧
      ∀ j, 0 < j.val → ordinalExpressionVariables (v j) = []

end LogicLineages.OrdinalComparison.Source.Targets
