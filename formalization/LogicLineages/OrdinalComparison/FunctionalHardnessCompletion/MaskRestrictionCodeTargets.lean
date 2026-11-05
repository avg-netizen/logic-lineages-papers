module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Targets

def ExactMasks : Prop := ∀ n : Nat,
  masksCode n = (masks n).map maskCode ∧ (masksCode n).length = 2^n ∧
    ∀ z : Mask n, maskCode z ∈ masksCode n

def ExactRestriction : Prop := ∀ (n : Nat) (z : Mask n) (d : SignedPair.Expression n),
  restrictCode (maskCode z) (SeededSourceCode.expressionCode d) =
    SeededSourceCode.expressionCode (restrict z d)

def ExactSystemRestriction : Prop := ∀ (n : Nat) (z : Mask n) (s : System n),
  restrictRows (maskCode z) (s.map SeededSourceCode.expressionCode) =
    (restrictSystem z s).map SeededSourceCode.expressionCode

/-- All raw list/natural inputs, not just well-formed masks or expressions. -/
def NumericalPrograms : Prop := Primrec extendMasks ∧ Primrec masksCode ∧
  Primrec₂ restrictCode ∧ Primrec₂ restrictRows

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Targets
