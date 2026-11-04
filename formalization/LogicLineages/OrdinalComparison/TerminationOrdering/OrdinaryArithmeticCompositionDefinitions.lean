module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticBetaDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic

open FirstOrder Language

/-- Quantify exactly the displayed finite block. This explicit Fin relabeling
uses no choice of an enumeration and leaves all original free variables free. -/
def existsFin {α : Type} {k : Nat} (p : Formula (α ⊕ Fin k)) : Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin k → α ⊕ Fin k) p).exs

def forallFin {α : Type} {k : Nat} (p : Formula (α ⊕ Fin k)) : Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin k → α ⊕ Fin k) p).alls

def applyGraph {n : Nat} {α : Type} (p : Formula (Fin (n + 1)))
    (out : Term α) (inputs : Fin n → Term α) : Formula α :=
  p.subst (Fin.cases out inputs)

def andFin {α : Type} {n : Nat} (p : Fin n → Formula α) : Formula α :=
  (List.ofFn p).foldr (· ⊓ ·) ⊤

/-- Ordinary strict order is an abbreviation for an existential addition
equation, not a new relation symbol. -/
def lessFormula {α : Type} (s t : Term α) : Formula α :=
  existsFin ((addTerm (s.relabel Sum.inl) (succTerm (.var (.inr (0 : Fin 1))))).equal
    (t.relabel Sum.inl))

/-- Intermediate values are the entire quantified Fin n block. Outputs occupy
free index0; source inputs occupy successor indices. -/
def compositionGraph {m n : Nat} (f : Formula (Fin (n + 1)))
    (g : Fin n → Formula (Fin (m + 1))) : Formula (Fin (m + 1)) :=
  existsFin ((applyGraph f (.var (.inl 0)) (fun i => .var (.inr i))) ⊓
    andFin (fun i => applyGraph (g i) (.var (.inr i))
      (fun j => .var (.inl j.succ))))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic
