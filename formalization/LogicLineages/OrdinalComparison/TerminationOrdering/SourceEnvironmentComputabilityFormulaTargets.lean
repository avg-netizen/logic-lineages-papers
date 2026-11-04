module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaTargets
open Source PositiveArithmeticOperators SourceComputabilityFormula SourceEnvironmentComputabilityFormula

def ActualEnvironmentFormulaAssembly : Prop := ∀ (formulas : Ty → language.Formula (Fin 2)) (Gamma : List Ty)
    (P : Nat → Prop) (context : Nat) (values : Fin Gamma.length → Nat),
  realize P (environmentFormula formulas Gamma) (Sum.elim (fun _ => context) values) ↔
    ∀ i : Fin Gamma.length, realize P (formulas (Gamma.get i)) ![context,values i]

def ActualEnvironmentComputabilityFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Delta : List Ty),
  ∃ formulas : Ty → language.Formula (Fin 2),
    (∀ tau P context value, realize P (formulas tau) ![context,value] ↔ Computable n arity Delta P context tau value) ∧
    (∀ (Gamma : List Ty) (P : Nat → Prop) (context : Nat) (values : Fin Gamma.length → Nat),
      realize P (environmentFormula formulas Gamma) (Sum.elim (fun _ => context) values) ↔
        ∀ i : Fin Gamma.length, Computable n arity Delta P context (Gamma.get i) (values i))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormulaTargets
