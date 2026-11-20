module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteComputabilityFormulaTargets
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowComputabilityFormulaTargets NumberedWindowAddressApplication
open NumberedWindowScalarAlgorithm (Settings)
def ConcreteTypeComputabilityFormula : Prop := ∀ s : Settings, ∃ p : Program 3,
  (∀ q u v, evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s q u v).toNat) ∧
    ∀ (τ : Ty) (α : Type) (q : OrdinaryArithmetic.Term α) (P : Nat → Prop) (env : α → Nat),
      realize P (formula p τ q) env ↔
        NumberedWindowComputabilityReading.holds (fun x a b => graph s x a b = true) P τ (q.realize env)
end LogicLineages.PersistentMarking.NumberedWindowConcreteComputabilityFormulaTargets
