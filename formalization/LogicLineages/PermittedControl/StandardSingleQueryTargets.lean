module
public import LogicLineages.PermittedControl.SelectedSingleQueryDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSingleQuery
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

/-- All natural inputs, literal one-query program, the unchanged displayed control
Phi and every genuine policy. -/
def ExactTotalReduction : Prop :=
  ∀ (policy : Policy) (strict : Bool) (e : Nat),
  ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
    packGroundQuery a b=SeededQueryCode.reduceCode strict e ∧
    (∀ τ ∈ Γ, τ.level≤1) ∧ SourceClasses.InternalLevelBound 3 a ∧
    SourceClasses.InternalLevelBound 3 b ∧
    (¬encodedPolynomialSolvable e ↔
      ∀ ρ : AdmissibleSubstitution Phi Γ, GroundComparison Phi policy strict a b ρ)

def BothReductions : Prop := ∀ policy : Policy,
  SelectedSingleQuery.SingleQueryReduction Phi policy true ∧
  SelectedSingleQuery.SingleQueryReduction Phi policy false

def StandardSingleQuery : Prop := LiteralPrograms ∧ ExactQueryCalibration ∧
  ExactWellFormed ∧ ExactTotalReduction ∧ BothReductions
end LogicLineages.PermittedControl.StandardSingleQuery
