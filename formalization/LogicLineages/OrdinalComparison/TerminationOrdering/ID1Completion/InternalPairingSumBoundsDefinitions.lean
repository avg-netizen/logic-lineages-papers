module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBounds
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph

/-- Weak arithmetic order using only the original embedded strict-order formula. -/
def weakBound {α : Type} (lower upper : OrdinaryArithmetic.Term α) : Formula α :=
  InternalLessThan.strictLess lower (OrdinaryArithmetic.succTerm upper)

/-- The unchanged original pairing graph, on arbitrary object-language terms. -/
def pairGraph {α : Type} (out left right : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph InternalPairing.pairing out (Fin.cons left (Fin.cons right Fin.elim0))

/-- Two child validator counts, each the original term payload plus one. -/
def childFuelSum {α : Type} (fp ap : OrdinaryArithmetic.Term α) : OrdinaryArithmetic.Term α :=
  OrdinaryArithmetic.addTerm (OrdinaryArithmetic.succTerm fp) (OrdinaryArithmetic.succTerm ap)

/-- The literal original application payload is pair 2 (pair d (pair fp ap)).
All intermediate values are shared internal graph witnesses. No outer packed
value, type-code bound, decoded validity, or standard-model equality is assumed. -/
def applicationPayloadWitnesses {α : Type}
    (payload middle children d fp ap : OrdinaryArithmetic.Term α) : Formula α :=
  pairGraph payload (OrdinaryArithmetic.succTerm
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)) middle ⊓
  (pairGraph middle d children ⊓ pairGraph children fp ap)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBounds
