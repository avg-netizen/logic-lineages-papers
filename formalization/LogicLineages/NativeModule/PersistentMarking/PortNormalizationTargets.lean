module

public import LogicLineages.NativeModule.PersistentMarking.PortNormalization

@[expose] public section

namespace LogicLineages.PersistentMarking.PortNormalizationTargets
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse PortNormalization RefinementRenamingTargets

def Erasure : Prop :=
 (∀ S K V Γ q t, PortComparison.Weak S K V Γ q t → Spine.Weak S q t) ∧
 (∀ S K V Γ q t, PortComparison.Strict S K V Γ q t → Spine.Strict S q t) ∧
 (∀ S K V Γ qs ts, PortComparison.Matching S K V Γ qs ts → Spine.Matching S qs ts) ∧
 (∀ S K V Γ qs ts, PortComparison.Multiset S K V Γ qs ts → Spine.Multiset S qs ts) ∧
 (∀ S K V Γ qs ts, PortComparison.Coverage S K V Γ qs ts → Spine.Coverage S qs ts) ∧
 (∀ S K V Γ f bs es ts, PortComparison.Whole S K V Γ f bs es ts → Spine.Whole S f bs es ts)

def ObservedUniverse : Prop := ∀ S (F : Inputs S) Γ q,
  WellFormed F.data.types F.data.ports Γ → Observed F Γ q →
  Universe F.data.types F.data.names (heads F.target) Γ q

def UnusedAbsent : Prop := ∀ K V H Γ q i σ,
  Universe K V H Γ q → Γ[i]? = some none → freeOccurs (σ,portName V i) q = false

def HeadObservations : Prop := ∀ S (F : Inputs S) Γ f bs,
  WellFormed F.data.types F.data.ports Γ → Observed F Γ (.head f bs) → ObservedArgs F Γ bs

def Normalization : Prop := ∀ S (F : Inputs S),
 (∀ q t, Spine.Weak S q t → WeakMotive F q t) ∧
 (∀ q t, Spine.Strict S q t → StrictMotive F q t) ∧
 (∀ qs ts, Spine.Matching S qs ts → MatchingMotive F qs ts) ∧
 (∀ qs ts, Spine.Multiset S qs ts → MultisetMotive F qs ts) ∧
 (∀ qs ts, Spine.Coverage S qs ts → CoverageMotive F qs ts) ∧
 (∀ f bs es ts, Spine.Whole S f bs es ts → WholeMotive F f bs es ts)
end LogicLineages.PersistentMarking.PortNormalizationTargets
