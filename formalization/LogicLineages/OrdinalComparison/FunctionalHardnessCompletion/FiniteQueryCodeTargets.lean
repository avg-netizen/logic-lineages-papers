module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Targets

def ExactQueryCalibration : Prop := ∀ (strict : Bool) (n : Nat) (s : System n),
  FunctionalHardnessCompletion.queryCode (groundQuery strict s) =
    queryCode strict n (s.map SeededSourceCode.expressionCode)

def ExactListCalibration : Prop := ∀ (strict : Bool) (n : Nat) (s : System n),
  (queries strict s).map FunctionalHardnessCompletion.queryCode =
    queriesCode strict n (s.map SeededSourceCode.expressionCode)

def PrimitivePrograms : Prop :=
  Primrec (fun p : Bool × Nat × List Nat => queryCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Bool × Nat × List Nat => queriesCode p.1 p.2.1 p.2.2) ∧ Primrec₂ reduceCode

/-- Every raw natural input has this exact computed output, genuine original
source queries, printed level-TWO bounds, and the complete universal equivalence. -/
def ExactTotalReduction : Prop := ∀ (strict : Bool) (e : Nat),
  ∃ qs : List GroundQuery, qs.map FunctionalHardnessCompletion.queryCode = reduceCode strict e ∧
    (∀ q ∈ qs, queryBounds 2 q) ∧
    (¬encodedPolynomialSolvable e ↔ ∀ q ∈ qs, queryUniversal strict q)

def ExistingReductions : Prop := FiniteQueryReduction true ∧ FiniteQueryReduction false

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Targets
