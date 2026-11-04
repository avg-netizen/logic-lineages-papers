module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransforms
open PositiveArithmeticOperators OrdinaryArithmetic

def relabel : {α β : Type} → (α → β) → Positive α → Positive β
  | _, _, g, .arithmetic phi => .arithmetic (phi.relabel g)
  | _, _, g, .predicate t => .predicate (t.relabel g)
  | _, _, g, .conj p q => .conj (relabel g p) (relabel g q)
  | _, _, g, .guarded guard p => .guarded (guard.relabel g) (relabel g p)
  | _, _, g, .all p => .all (relabel (Sum.map g id) p)

def tagNumber (odd : Bool) (x : Nat) : Nat := if odd then 2*x+1 else 2*x

def tagTerm {α : Type} (odd : Bool) (t : Term α) : Term α :=
  let twice := mulTerm (succTerm (succTerm zeroTerm)) t
  if odd then succTerm twice else twice

def tagPredicate (odd : Bool) : {α : Type} → Positive α → Positive α
  | _, .arithmetic phi => .arithmetic phi
  | _, .predicate t => .predicate (tagTerm odd t)
  | _, .conj p q => .conj (tagPredicate odd p) (tagPredicate odd q)
  | _, .guarded guard p => .guarded guard (tagPredicate odd p)
  | _, .all p => .all (tagPredicate odd p)

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransforms
