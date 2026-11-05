module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Targets
open OriginalDomain SourceClasses

def ExactQueryCalibration : Prop := ∀ (strict : Bool) (n : Nat) (s : System n),
  packGroundQuery (sourcePair strict s).1 (sourcePair strict s).2 =
    queryCode strict n (s.map SeededSourceCode.expressionCode)

def ExactWellFormed : Prop := ∀ c : SystemCode, validSystem c = true ↔ WellFormedCode c

def PrimitivePrograms : Prop :=
  Primrec₂ validRow ∧ Primrec validSystem ∧
  Primrec (fun p : Bool × Nat × List Nat => queryCode p.1 p.2.1 p.2.2) ∧ Primrec₂ reduceCode

/-- Literal computed output, all natural inputs, actual sources, printed type
bounds, and both strictness conventions. No undecidability supplier is assumed. -/
def ExactTotalReduction : Prop := ∀ (strict : Bool) (e : Nat),
  ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
    packGroundQuery a b = reduceCode strict e ∧ (∀ τ ∈ Γ, τ.level ≤ 1) ∧
      InternalLevelBound 3 a ∧ InternalLevelBound 3 b ∧
      (¬encodedPolynomialSolvable e ↔ ∀ ρ : AdmissibleSubstitution Γ, GroundComparison strict a b ρ)

/-- The unchanged existing level-three reduction obligations, separated from
the still-pending level-two reductions and genuine undecidability theorem. -/
def ExistingReductions : Prop := SingleQueryReduction true ∧ SingleQueryReduction false

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Targets
