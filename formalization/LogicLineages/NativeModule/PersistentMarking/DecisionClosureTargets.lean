module

public import LogicLineages.NativeModule.PersistentMarking.DecisionRequests

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionClosureTargets
open Spine NameBridge PortNormalization DecisionRequests

def InitialState : Prop := ∀ S (F : Inputs S),
  Invariant F (.weak (blank F.data.ports) F.source F.target) ∧
  Invariant F (.strict (blank F.data.ports) F.source F.target)

def InitialEquivalence : Prop := ∀ S (F : Inputs S),
  (Spine.Weak S F.source F.target ↔
    PortComparison.Weak S F.data.types F.data.names (blank F.data.ports) F.source F.target) ∧
  (Spine.Strict S F.source F.target ↔
    PortComparison.Strict S F.data.types F.data.names (blank F.data.ports) F.source F.target)

def ChildPreservation : Prop := ∀ S (F : Inputs S) parent child,
  Child S F.data.types F.data.names parent child → Invariant F parent → Invariant F child

/- A failed full call is still a reachable request, not a discarded failed
comparison proof. Every domain/suffix type is included by the actual call
source type and the subtype-closed input inventory. -/
def CallRequestedTypes : Prop := ∀ S (F : Inputs S) Γ q σ args τ t,
  Invariant F (.fullCall Γ q σ args τ t) →
  (∀ υ, υ ∈ TypeSupport.subtypes σ → υ ∈ F.data.types) ∧
  (∀ υ, υ ∈ TypeSupport.subtypes τ → υ ∈ F.data.types)

def FullClosure : Prop := ∀ S (F : Inputs S),
  (Spine.Weak S F.source F.target ↔
    PortComparison.Weak S F.data.types F.data.names (blank F.data.ports) F.source F.target) ∧
  (Spine.Strict S F.source F.target ↔
    PortComparison.Strict S F.data.types F.data.names (blank F.data.ports) F.source F.target) ∧
  (∀ request, Reach S F.data.types F.data.names
    (.weak (blank F.data.ports) F.source F.target) request → Invariant F request) ∧
  (∀ request, Reach S F.data.types F.data.names
    (.strict (blank F.data.ports) F.source F.target) request → Invariant F request) ∧
  (∀ Γ q σ args τ t, Reach S F.data.types F.data.names
    (.weak (blank F.data.ports) F.source F.target) (.fullCall Γ q σ args τ t) →
    (∀ υ, υ ∈ TypeSupport.subtypes σ → υ ∈ F.data.types) ∧
    (∀ υ, υ ∈ TypeSupport.subtypes τ → υ ∈ F.data.types))
end LogicLineages.PersistentMarking.DecisionClosureTargets
