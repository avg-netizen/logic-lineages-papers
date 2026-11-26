import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextBits
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticRawWitnessCodeTargets

/-- Independent actual quotient carriers, not definitions by accepting
an address or path checker. Each input scope is its actual finiteC. -/
def AdmittedAddress (S : Signature) (K : List Ty) (n : Nat) : Prop :=
  ∃ Γ τ least (x : Class S K (finiteC Γ) τ),
    encodeAddress ⟨Γ,τ,least⟩ = n ∧ ActualCodeAt S K Γ τ least x

def AddressPositive (S : Signature) (K : List Ty) (src dst : Nat) : Prop :=
  ∃ Γ τ i j (x y : Class S K (finiteC Γ) τ),
    encodeAddress ⟨Γ,τ,i⟩ = src ∧ encodeAddress ⟨Γ,τ,j⟩ = dst ∧
      ActualCodeAt S K Γ τ i x ∧ ActualCodeAt S K Γ τ j y ∧
      RS S K (finiteC Γ) τ x y

def ExactClassAddressCodec : Prop := LiteralWitnessCodec encodeAddress decodeAddress

def ExactCanonicalAddressBit : Prop :=
  ∀ S K (a : ClassAddress), DecisionSourceUniverse.Closed K →
    (canonicalBit S K a = true ↔
      ∃ x : Class S K (finiteC a.context) a.result, ActualCodeAt S K a.context a.result a.least x)

def ExactAdmittedAddressBit : Prop :=
  ∀ S K n, DecisionSourceUniverse.Closed K →
    (addressBit S K n = true ↔ AdmittedAddress S K n)

def ExactAddressPositivePath : Prop :=
  ∀ S K src dst, DecisionSourceUniverse.Closed K →
    ((∃ cert, addressRSBit S K src cert dst = true) ↔ AddressPositive S K src dst)

def ActualAddressPathDomain : Prop :=
  ∀ S K src dst, AddressPositive S K src dst →
    AdmittedAddress S K src ∧ AdmittedAddress S K dst

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets
