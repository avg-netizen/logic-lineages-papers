import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddress
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets

namespace LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressTargets
open Spine NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowDirectClassAddress NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticLeastClass

/-- Independent direct class checker, with the original literal edge
certificate and the same complete context and result type on both sides. -/
def literalDirect (S : Signature) (K : List Ty) (source certificate target : Nat) : Bool :=
  match decodeAddress source, decodeAddress target with
  | some a, some b =>
    decide (a.context = b.context) && decide (a.result = b.result) &&
      classEdgeCodeBit S K a.context a.result a.least certificate b.least
  | _, _ => false

def DirectClassAddress (S : Signature) (K : List Ty) (source target : Nat) : Prop :=
  ∃ (Γ : List Ty) (τ : Ty) (i j : Nat) (q r : Class S K (finiteC Γ) τ),
    encodeAddress ⟨Γ,τ,i⟩ = source ∧ encodeAddress ⟨Γ,τ,j⟩ = target ∧
      ActualCodeAt S K Γ τ i q ∧ ActualCodeAt S K Γ τ j r ∧ ClassEdge q r

def ExactDirectAddressBit : Prop :=
  ∀ (S : Signature) (K : List Ty) (positive : Nat → Nat → Nat → Bool),
    positive = addressRSBit S K → directAddress positive = literalDirect S K

def ExactDirectClassAddress : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ source target, (∃ certificate, literalDirect S K source certificate target = true) ↔
      DirectClassAddress S K source target

end LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressTargets
