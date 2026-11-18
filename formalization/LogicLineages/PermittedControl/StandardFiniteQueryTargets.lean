module
public import LogicLineages.PermittedControl.SelectedFiniteQueryDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFiniteQuery
open OrdinalComparison Source SelectedSourceDomain SelectedFiniteQuery
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (GroundQuery queryCode queryBounds encodedPolynomialSolvable)

/-- Literal executable total map, not an existentially chosen semantic list. -/
def ExactTotalReduction : Prop := ∀ (policy : Policy) (strict : Bool) (e : Nat),
    ∃ qs : List GroundQuery,
      qs.map queryCode=FunctionalHardnessCompletion.FiniteQueryCode.reduceCode strict e ∧
      (∀ q ∈ qs, queryBounds 2 q) ∧
      (¬encodedPolynomialSolvable e ↔ ∀ q ∈ qs, queryUniversal Phi policy strict q)

def LiteralProgram : Prop := Primrec₂ FunctionalHardnessCompletion.FiniteQueryCode.reduceCode

def BothReductions : Prop := ∀ policy : Policy,
  FiniteQueryReduction Phi policy true ∧ FiniteQueryReduction Phi policy false

def StandardFiniteQuery : Prop := LiteralProgram ∧ ExactTotalReduction ∧ BothReductions
end LogicLineages.PermittedControl.StandardFiniteQuery
