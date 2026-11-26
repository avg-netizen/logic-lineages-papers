module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNumeralGraphTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof

def inputs {α : Type} {n : Nat} (v : List.Vector Nat n) : Fin n → OrdinaryArithmetic.Term α :=
  fun i => numeral (v.get i)

/-- A finite internal proof at each supplied tuple of numerals for the
original arity-indexed program and the original arithmetic graph compiler. -/
def NumeralGraph : Prop :=
  ∀ n (p : Program n) (v : List.Vector Nat n) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)),
    Nonempty (Derivation body Γ (programGraph p (numeral (evaluate p v)) (inputs v)))

end LogicLineages.PersistentMarking.NumberedWindowNumeralGraphTargets
