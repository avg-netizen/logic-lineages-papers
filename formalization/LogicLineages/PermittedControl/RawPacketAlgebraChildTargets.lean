module
public import LogicLineages.PermittedControl.RawPacketAlgebraReifyTargets
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open PreparedProjection (PreparedPacketCode)
open ActualPreparedSlotAppend (Packet)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (lowerFamily)
open ActualGuardedResidualBitFamily (reifyFamily)
open ActualBitFamilyRawLayout (RawFamily encodeFamily)

/-- The assembled raw residual program of `StageCallbackSupplier.child`, generic
in the supplier's (un-prepended) packet codes: predecessor guard, projection
at `C`, decoding, keep, reification, all on codes. -/
def childCode (x : Nat × Nat × List PreparedPacketCode) : RawFamily :=
  reifyFamilyCode x.1 x.2.1 (lowerFamilyCode x.2.1 x.1 (x.2.2.map (prependCode x.2.1)))

/-- Literal equation for every packet list, no shape hypothesis. -/
def ExactChildCode : Prop :=
  ∀ (C top : Nat) (qs : List Packet),
    childCode (C,top,qs.map encodePacket) =
      encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top))))

def ChildEffectivity : Prop := Primrec childCode ∧ Computable childCode

def FullRawPacketAlgebraChild : Prop := ExactChildCode ∧ ChildEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
