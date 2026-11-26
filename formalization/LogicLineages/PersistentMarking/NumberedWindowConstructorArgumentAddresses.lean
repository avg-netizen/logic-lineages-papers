import LogicLineages.PersistentMarking.NumberedWindowExternalComputability
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperators

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddresses
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticClassAddress NumberedWindowExternalComputability

def slot (S : Signature) (K Γ : List Ty) (q : NTerm) : Option Nat :=
  (leastCode S K Γ q.type q).map (fun i => encodeAddress ⟨Γ,q.type,i⟩)

/-- Exact position-by-position correspondence; every successful address is
the one returned by the original partial least-code computation. -/
def Slots (S : Signature) (K Γ : List Ty) (xs : NArgs) (codes : List Nat) : Prop :=
  xs.toList.map (slot S K Γ) = codes.map some

def ComputableArgument (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K) (q : NTerm) : Prop :=
  ∃ h : InWindow S K (finiteC Γ) q.type q, ComputableClass S K Γ hk q.type (classOf ⟨q,h⟩)

end LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddresses
