import LogicLineages.PersistentMarking.NumberedWindowPathWitnessBits
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClass

namespace LogicLineages.PersistentMarking.NumberedWindowClassPathWitnessBits
open Spine NumberedWindowSyntax NumberedWindowRawWitnessBits NumberedWindowArithmeticLeastClass

/-- Original raw representatives and a genuine edge proof certificate.
Representatives for consecutive edges need not be literally equal. -/
structure ClassEdgeWitness where
  source : NTerm
  target : NTerm
  witness : RawWitness

/-- Require actual successful least codes of independently admitted raw
endpoints. Equality of two absent codes is never a witness. -/
def classEdgeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src dst : Nat) (e : ClassEdgeWitness) : Bool :=
  finiteWindowWitnessBit S K Γ τ e.witness e.source e.target &&
    decide (leastCode S K Γ τ e.source = some src) &&
    decide (leastCode S K Γ τ e.target = some dst)

structure ClassHop where
  targetCode : Nat
  edge : ClassEdgeWitness

/-- Match consecutive actual class codes while retaining every raw edge. -/
def classWalkBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty) :
    Nat → List ClassHop → Nat → Bool
  | src, [], dst => decide (src = dst)
  | src, e :: es, dst =>
    classEdgeBit S K Γ τ src e.targetCode e.edge &&
      classWalkBit S K Γ τ e.targetCode es dst

/-- The original RS is positive: the internal equality-only terminal
case is never by itself accepted as an RS certificate. -/
def positiveClassPathBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src : Nat) (es : List ClassHop) (dst : Nat) : Bool :=
  !es.isEmpty && classWalkBit S K Γ τ src es dst

end LogicLineages.PersistentMarking.NumberedWindowClassPathWitnessBits
