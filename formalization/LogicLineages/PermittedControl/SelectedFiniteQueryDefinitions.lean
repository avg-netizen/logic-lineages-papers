module
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFiniteQuery
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (GroundQuery queryCode queryBounds packGroundQuery)

def GroundComparison {Γ : List Ty} (ctrl : Nat → Nat) (policy : Policy) (strict : Bool)
    (a b : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution ctrl Γ) : Prop :=
  if strict then groundValue ctrl policy ρ a<groundValue ctrl policy ρ b
  else groundValue ctrl policy ρ a≤groundValue ctrl policy ρ b

def queryUniversal (ctrl : Nat → Nat) (policy : Policy) (strict : Bool) (q : GroundQuery) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl q.1, GroundComparison ctrl policy strict q.2.1 q.2.2 ρ

def FiniteQueryReduction (ctrl : Nat → Nat) (policy : Policy) (strict : Bool) : Prop :=
  ∃ reduce : Nat → List Nat, Computable reduce ∧ ∀ e : Nat,
    ∃ qs : List GroundQuery, qs.map queryCode=reduce e ∧
      (∀ q ∈ qs, queryBounds 2 q) ∧
      (¬FunctionalHardnessCompletion.encodedPolynomialSolvable e ↔
        ∀ q ∈ qs, queryUniversal ctrl policy strict q)

/-- Public decider domain is all actual sources satisfying the printed bounds. -/
def HasComparisonDecider (ctrl : Nat → Nat) (policy : Policy) (level : Nat) (strict : Bool) : Prop :=
  ∃ decideQuery : Nat → Bool, Computable decideQuery ∧
    ∀ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      (∀ τ ∈ Γ, τ.level≤1) → SourceClasses.InternalLevelBound level a →
      SourceClasses.InternalLevelBound level b →
      (decideQuery (packGroundQuery a b)=true ↔
        ∀ ρ : AdmissibleSubstitution ctrl Γ, GroundComparison ctrl policy strict a b ρ)
end LogicLineages.PermittedControl.SelectedFiniteQuery
