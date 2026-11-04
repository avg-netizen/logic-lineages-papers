module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsProof
public import Mathlib.Data.Finset.Card
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompleteness
def StrictTotalTable {n : Nat} (table : Fin n → Fin n → Bool) : Prop :=
  (∀ f, table f f = false) ∧
  (∀ f g h, table f g = true → table g h = true → table f h = true) ∧
  (∀ f g, f ≠ g → table f g = true ∨ table g f = true)

def lowerSet {n : Nat} (table : Fin n → Fin n → Bool) (f : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun g => table f g = true)
end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceCompleteness
