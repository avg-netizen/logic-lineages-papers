module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaTargets
open Source SourceComputabilityFormula PositiveArithmeticOperators

def ActualGeneralFormulaCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty), ∃ formulas : Ty → language.Formula (Fin 2),
    ∀ (tau : Ty) (P : Nat → Prop) (context x : Nat),
      realize P (formulas tau) ![context,x] ↔ Computable n arity Gamma P context tau x

def ActualComputabilityTypedness : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (P : Nat → Prop) (context : Nat) (tau : Ty) (x : Nat),
    Computable n arity Gamma P context tau x →
    OrdinaryArithmeticTypedCarrier.encodedTyped n arity Gamma context
      (NumberedLeastCodeRepresentative.typeNumber tau) x

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaTargets
