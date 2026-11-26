module
public import LogicLineages.PermittedControl.SelectedAggregationDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAggregationTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector SelectedAggregation
open OrdinalComparison.ParametricActualCollapse

def SixEraserCollision : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ .ground),
  let l := SourceCollisionCompletion.detectorLeft a b
  let r := SourceCollisionCompletion.detectorRight a b
  GroundResult ctrl policy ρ l ∧ GroundResult ctrl policy ρ r ∧
  groundValue ctrl policy ρ r≤groundValue ctrl policy ρ l ∧
  (groundValue ctrl policy ρ l=groundValue ctrl policy ρ r ↔
    groundValue ctrl policy ρ a=groundValue ctrl policy ρ b) ∧
  (groundValue ctrl policy ρ a≠groundValue ctrl policy ρ b →
    groundValue ctrl policy ρ r+2≤groundValue ctrl policy ρ l)

def ActualAggregation : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ),
  (∀ es, AggregateAt ctrl policy ρ es) ∧
  groundValue ctrl policy ρ (SourceAggregateCompletion.aggregate ([] : List
    (OriginalTerm Γ .ground × OriginalTerm Γ .ground))).1=1 ∧
  groundValue ctrl policy ρ (SourceAggregateCompletion.aggregate ([] : List
    (OriginalTerm Γ .ground × OriginalTerm Γ .ground))).2=1

def ActualWeakConversion : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (l r : OriginalTerm Γ .ground),
  let kr := ParametricLiteralWeakWrapper.constantApply r
  let il := ParametricLiteralWeakWrapper.identityApply l
  GroundResult ctrl policy ρ kr ∧ GroundResult ctrl policy ρ il ∧
  groundValue ctrl policy ρ kr=collapseWith ctrl
    (Ordinal.omega0+((5+groundValue ctrl policy ρ r : Nat) : Ordinal)) ∧
  groundValue ctrl policy ρ il=collapseWith ctrl
    (Ordinal.omega0+((3+groundValue ctrl policy ρ l : Nat) : Ordinal)) ∧
  (groundValue ctrl policy ρ kr≤groundValue ctrl policy ρ il ↔
    groundValue ctrl policy ρ r+2≤groundValue ctrl policy ρ l)

def AggregateWeakQuery : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
  let pair := SourceAggregateCompletion.aggregate es
  (groundValue ctrl policy ρ pair.2<groundValue ctrl policy ρ pair.1 ↔
    ¬AllEqual ctrl policy ρ es) ∧
  (groundValue ctrl policy ρ (ParametricLiteralWeakWrapper.constantApply pair.2)≤
    groundValue ctrl policy ρ (ParametricLiteralWeakWrapper.identityApply pair.1) ↔
    ¬AllEqual ctrl policy ρ es)

def SelectedAggregation : Prop := SixEraserCollision ∧ ActualAggregation ∧
  ActualWeakConversion ∧ AggregateWeakQuery
end LogicLineages.PermittedControl.SelectedAggregationTargets
