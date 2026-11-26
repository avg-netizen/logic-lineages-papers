module
public import LogicLineages.PermittedControl.SelectedFiniteQueryDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFiniteQueryTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFiniteQuery
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (GroundQuery queryCode queryBounds encodedPolynomialSolvable)

/-- Literal executable total map, not an existentially chosen semantic list. -/
def ExactTotalReduction : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (strict : Bool) (e : Nat),
    ∃ qs : List GroundQuery,
      qs.map queryCode=FunctionalHardnessCompletion.FiniteQueryCode.reduceCode strict e ∧
      (∀ q ∈ qs, queryBounds 2 q) ∧
      (¬encodedPolynomialSolvable e ↔ ∀ q ∈ qs, queryUniversal ctrl policy strict q)

def LiteralProgram : Prop := Primrec₂ FunctionalHardnessCompletion.FiniteQueryCode.reduceCode

def BothReductions : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K → ∀ policy : Policy,
  FiniteQueryReduction ctrl policy true ∧ FiniteQueryReduction ctrl policy false

def SelectedFiniteQuery : Prop := LiteralProgram ∧ ExactTotalReduction ∧ BothReductions
end LogicLineages.PermittedControl.SelectedFiniteQueryTargets
