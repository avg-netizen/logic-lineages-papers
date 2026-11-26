module
public import LogicLineages.PermittedControl.SelectedAggregationDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardAggregation
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector SelectedAggregation
open Source.AdmissibleSum
open OrdinalComparison.ParametricActualCollapse

def SixEraserCollision : Prop := ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ .ground),
  let l := SourceCollisionCompletion.detectorLeft a b
  let r := SourceCollisionCompletion.detectorRight a b
  GroundResult Phi policy ρ l ∧ GroundResult Phi policy ρ r ∧
  groundValue Phi policy ρ r≤groundValue Phi policy ρ l ∧
  (groundValue Phi policy ρ l=groundValue Phi policy ρ r ↔
    groundValue Phi policy ρ a=groundValue Phi policy ρ b) ∧
  (groundValue Phi policy ρ a≠groundValue Phi policy ρ b →
    groundValue Phi policy ρ r+2≤groundValue Phi policy ρ l)

def ActualAggregation : Prop := ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ),
  (∀ es, AggregateAt Phi policy ρ es) ∧
  groundValue Phi policy ρ (SourceAggregateCompletion.aggregate ([] : List
    (OriginalTerm Γ .ground × OriginalTerm Γ .ground))).1=1 ∧
  groundValue Phi policy ρ (SourceAggregateCompletion.aggregate ([] : List
    (OriginalTerm Γ .ground × OriginalTerm Γ .ground))).2=1

def ActualWeakConversion : Prop := ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (l r : OriginalTerm Γ .ground),
  let kr := ParametricLiteralWeakWrapper.constantApply r
  let il := ParametricLiteralWeakWrapper.identityApply l
  GroundResult Phi policy ρ kr ∧ GroundResult Phi policy ρ il ∧
  groundValue Phi policy ρ kr=collapseWith Phi
    (Ordinal.omega0+((5+groundValue Phi policy ρ r : Nat) : Ordinal)) ∧
  groundValue Phi policy ρ il=collapseWith Phi
    (Ordinal.omega0+((3+groundValue Phi policy ρ l : Nat) : Ordinal)) ∧
  (groundValue Phi policy ρ kr≤groundValue Phi policy ρ il ↔
    groundValue Phi policy ρ r+2≤groundValue Phi policy ρ l)

def AggregateWeakQuery : Prop := ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
  let pair := SourceAggregateCompletion.aggregate es
  (groundValue Phi policy ρ pair.2<groundValue Phi policy ρ pair.1 ↔
    ¬AllEqual Phi policy ρ es) ∧
  (groundValue Phi policy ρ (ParametricLiteralWeakWrapper.constantApply pair.2)≤
    groundValue Phi policy ρ (ParametricLiteralWeakWrapper.identityApply pair.1) ↔
    ¬AllEqual Phi policy ρ es)

def StandardAggregation : Prop := SixEraserCollision ∧ ActualAggregation ∧
  ActualWeakConversion ∧ AggregateWeakQuery
end LogicLineages.PermittedControl.StandardAggregation
