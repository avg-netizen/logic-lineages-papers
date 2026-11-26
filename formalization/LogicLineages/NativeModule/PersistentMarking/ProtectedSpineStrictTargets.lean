module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLawTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineStrictTargets
open Spine DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineEnvironment (freeCode boundCode)

def StrictlessInputs (E : Environment) (Γ : Context) (a : Assignments) : Prop :=
  ∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ → ∀ σ t,
    t ∈ observations E.names E.ports Δ E.target σ →
    (∀ x, (decode E σ Γ (freeCode E Γ a.free σ x)).strict Δ t = false) ∧
    (∀ i, (decode E σ Γ (boundCode E Γ a.bound σ i)).strict Δ t = false)

def MarkingFields : Prop := ∀ S E H M Γ Δ a q t,
  Covered E H q → InputValid E Γ a → StrictlessInputs E Γ a →
  WellFormed E.types E.ports Δ → Extends Γ Δ →
  t ∈ observations E.names E.ports Δ E.target q.type →
  (valueAt (evaluate S E H M q) Γ a).strict Δ t =
    match mark q with
    | none => false
    | some r => (valueAt (evaluate S E H M r) Γ a).weak Δ t

end LogicLineages.PersistentMarking.ProtectedSpineStrictTargets
