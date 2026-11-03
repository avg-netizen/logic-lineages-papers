module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedFiniteUniverse

/-- The original window decision, uniformly in both finite window lists and the literal head code. -/
def ActualHeadWindowPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
    decide (HeadInWindow arity p.1 p.2.1 (decodeHead p.2.2)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecTargets
