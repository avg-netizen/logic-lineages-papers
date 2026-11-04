module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaTargets
open Source PositiveArithmeticOperators SourceComputabilityFormula NumberedLeastCodeRepresentative SourceFiniteComputabilityFormula

def ActualFiniteFormulaAssembly : Prop := ∀ (formulas : Ty → language.Formula (Fin 2)) (S : List Ty)
    (P : Nat → Prop) (context typ value : Nat),
  realize P (windowFormula formulas S) ![context,typ,value] ↔
    ∃ tau ∈ S, typ = typeNumber tau ∧ realize P (formulas tau) ![context,value]

def ActualWindowComputabilityFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ formulas : Ty → language.Formula (Fin 2),
    (∀ tau P context value, realize P (formulas tau) ![context,value] ↔ Computable n arity Gamma P context tau value) ∧
    (∀ (S : List Ty) P context typ value,
      realize P (windowFormula formulas S) ![context,typ,value] ↔
        ∃ tau ∈ S, typ = typeNumber tau ∧ Computable n arity Gamma P context tau value) ∧
    (∀ (S : List Ty) P context typ value, NumberedNumericDecoding.decodeType typ = none →
      ¬ realize P (windowFormula formulas S) ![context,typ,value])

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaTargets
