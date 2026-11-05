module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Targets
open CircuitLinear Narendran LogicLineages.ComputabilityKnowledge.CircuitReduction
open LogicLineages.ComputabilityKnowledge.PositiveExpression

def ExactAllocation : Prop := ∀ n g : Nat,
  Function.Injective (@slotIndex n g) ∧ ∀ s : Slot n g, slotIndex s<unknownCount n g

/-- Equality is computed by the original positive circuit run, not by an
assumed evaluator or a newly defined tautological source predicate. -/
def ScalarRunSemantics : Prop := ∀ c : Circuit, c.WellFormed →
  ((∃ ρ : Nat → PosNat, c.outputEqual ρ) ↔ ∃ v : Nat → Nat, ScalarSolution c v)

/-- Forward direction allocates all row witnesses in one global polynomial
assignment, preserving every original scalar wire exactly. -/
def LiteralRowsForward : Prop := ∀ (c : Circuit), c.WellFormed →
  ∀ v : Nat → Nat, ScalarSolution c v →
    ∃ p : Nat → NPolynomial,
      (∀ i, i<c.inputCount+c.gates.length → p i=Polynomial.C (v i)) ∧
      RowsSolve p (encodeCircuitSystem c).2

/-- Backward direction extracts the same scalar assignment at every occurrence;
positivity is forced by the original input-slack rows. -/
def LiteralRowsBackward : Prop := ∀ (c : Circuit), c.WellFormed →
  ∀ p : Nat → NPolynomial, RowsSolve p (encodeCircuitSystem c).2 →
    ∃ v : Nat → Nat, ScalarSolution c v ∧
      ∀ i, i<c.inputCount+c.gates.length → p i=Polynomial.C (v i)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Targets
