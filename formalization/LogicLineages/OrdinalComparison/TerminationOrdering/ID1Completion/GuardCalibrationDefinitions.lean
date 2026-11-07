module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibration
open Source

/-- A total numeric extractor. The original context input is deliberately
ignored; the outer pairing is the EXISTING object code and the inner pairing
is the EXISTING packed-number code. -/
def typeTag (_context object : Nat) : Nat := (Nat.unpair (Nat.unpair object).2).1

def typeTagValue (v : List.Vector Nat 2) : Nat := typeTag (v.get 0) (v.get 1)

/-- A finite Boolean test of closure under the ORIGINAL type subexpressions. -/
def subtypeClosedTest (S : List Ty) : Bool :=
  S.all (fun sigma => sigma.subtypes.all (fun tau => decide (tau ∈ S)))

/-- The original Context decoder and original type window. A malformed
context or nonclosed window yields zero. No source checker is modified. -/
def validWindow (n context : Nat) : Nat :=
  ((Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context).any
    (fun ctx => subtypeClosedTest ctx.1.2)).toNat

def validWindowValue (n : Nat) (v : List.Vector Nat 1) : Nat := validWindow n (v.get 0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibration
