module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Targets
open SignedPair SeededSourceCode

/-- Equality includes rejected out-of-range references, not only valid rows. -/
def ExactMonomialCode : Prop := ∀ (n : Nat) (m : MonomialCode),
  monomialCode n m = (monomialOfCode n m).map
    (fun t => expressionCode (monomialExpression t))

def ExactRows : Prop := ∀ (n : Nat) (row : List MonomialCode),
  rowCode n row = expressionCode (fromMonomials (row.filterMap (monomialOfCode n)))

def ExactSubtractSeed : Prop := ∀ (n : Nat) (d : Expression n),
  subtractSeedCode n (expressionCode d) = expressionCode (SeededCompiler.subtractSeed d)

/-- Exactly the archived input-system decoder, including its specified filter.
This does not assert malformed codes are satisfiable or valid source instances. -/
def ExactSystemInputs : Prop := ∀ c : SystemCode,
  inputCode c = (systemOfCode c).map expressionCode ∧
  seededInputCode c = (systemOfCode c).map
    (fun d => expressionCode (SeededCompiler.subtractSeed d))

def NumericalPrograms : Prop :=
  Primrec expandMonomial ∧ Primrec₂ validMonomial ∧ Primrec₂ monomialCode ∧
  Primrec₂ rowCode ∧ Primrec₂ subtractSeedCode ∧ Primrec inputCode ∧ Primrec seededInputCode

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Targets
