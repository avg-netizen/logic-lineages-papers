module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrec
open NumberedAuxiliaryCoding

/-- Literal structural size and maximum finite label, counting term constructors
but not argument-list constructors, exactly as in the original typed syntax. -/
def codeBounds {Symbol : Type} : Code Symbol → Nat × Nat
  | .var _ => (1, 0)
  | .lam _ body =>
    let bounds := codeBounds body
    (1 + bounds.1, bounds.2)
  | .app _ q a =>
    let qb := codeBounds q
    let ab := codeBounds a
    (1 + qb.1 + ab.1, max qb.2 ab.2)
  | .bottom _ => (1, 0)
  | .ordinary _ base =>
    let bounds := codeBounds base
    (1 + bounds.1, bounds.2)
  | .numbered k _ _ base _ extras =>
    let bb := codeBounds base
    let eb := codeBounds extras
    (1 + bb.1 + eb.1, max k (max bb.2 eb.2))
  | .argumentsNil => (0, 0)
  | .argumentsCons _ q rest =>
    let qb := codeBounds q
    let rb := codeBounds rest
    (qb.1 + rb.1, max qb.2 rb.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrec
