module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocks
open FirstOrder Language PositiveArithmeticOperators InternalCalculus

/-- The EXISTING bounded-syntax existential block, without a new quantifier. -/
abbrev block {α : Type} {k : Nat} (phi : Formula (α ⊕ Fin k)) : Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin k → α ⊕ Fin k) phi).exs

def eraseZero {α : Type} : α ⊕ Fin 0 → α := Sum.elim id Fin.elim0

/-- Keep the first k variables in order, expose the LAST variable as a singleton. -/
def splitLast {α : Type} (k : Nat) : α ⊕ Fin (k + 1) → (α ⊕ Fin k) ⊕ Fin 1 :=
  Sum.elim (fun a => .inl (.inl a))
    (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocks
