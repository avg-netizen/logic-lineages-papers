module
public import LogicLineages.PermittedControl.SelectedSingleQueryDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSingleQueryTargets
open OrdinalComparison Source SelectedSourceDomain Source.AdmissibleSum SelectedFiniteQuery
open Source.FunctionalHardnessCompletion

def LiteralPrograms : Prop :=
  Primrec₂ SeededQueryCode.validRow ∧ Primrec SeededQueryCode.validSystem ∧
  Primrec (fun p : Bool × Nat × List Nat => SeededQueryCode.queryCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ SeededQueryCode.reduceCode

def ExactQueryCalibration : Prop := ∀ (strict : Bool) (n : Nat) (s : System n),
  packGroundQuery (SeededQueryCode.sourcePair strict s).1 (SeededQueryCode.sourcePair strict s).2=
    SeededQueryCode.queryCode strict n (s.map SeededSourceCode.expressionCode)

def ExactWellFormed : Prop := ∀ c : SystemCode,
  SeededQueryCode.validSystem c=true ↔ WellFormedCode c

/-- All natural inputs, literal one-query program, every selected control and policy. -/
def ExactTotalReduction : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (strict : Bool) (e : Nat),
  ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
    packGroundQuery a b=SeededQueryCode.reduceCode strict e ∧
    (∀ τ ∈ Γ, τ.level≤1) ∧ SourceClasses.InternalLevelBound 3 a ∧
    SourceClasses.InternalLevelBound 3 b ∧
    (¬encodedPolynomialSolvable e ↔
      ∀ ρ : AdmissibleSubstitution ctrl Γ, GroundComparison ctrl policy strict a b ρ)

def BothReductions : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K → ∀ policy : Policy,
  SelectedSingleQuery.SingleQueryReduction ctrl policy true ∧
  SelectedSingleQuery.SingleQueryReduction ctrl policy false

def SelectedSingleQuery : Prop := LiteralPrograms ∧ ExactQueryCalibration ∧
  ExactWellFormed ∧ ExactTotalReduction ∧ BothReductions
end LogicLineages.PermittedControl.SelectedSingleQueryTargets
