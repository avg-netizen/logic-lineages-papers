import LogicLineages.PersistentMarking.DecisionPorts
namespace LogicLineages.PersistentMarking.DecisionPortsTargets
open Spine NameBridge DecisionPorts

def EnumerationExact : Prop := ∀ K B Γ, Γ ∈ contexts K B ↔ WellFormed K B Γ
def ExtensionReflexive : Prop := ∀ Γ, Extends Γ Γ
def ExtensionTransitive : Prop := ∀ Γ Δ Θ, Extends Γ Δ → Extends Δ Θ → Extends Γ Θ
def UsedBound : Prop := ∀ Γ, used Γ ≤ Γ.length
def UsedMonotone : Prop := ∀ Γ Δ, Extends Γ Δ → used Γ ≤ used Δ
def UnusedExists : Prop := ∀ Γ, used Γ < Γ.length → ∃ i, Γ[i]? = some none
def PortFresh : Prop := ∀ V i σ, (σ,portName V i) ∉ V
def PortInjective : Prop := ∀ V i j, portName V i = portName V j → i = j
def ValuesExact : Prop := ∀ V Γ σ q, q ∈ values V Γ σ ↔ AtPort V Γ σ q
def ValuesTyped : Prop := ∀ V Γ σ q, q ∈ values V Γ σ → Typed EmptyContext q σ
def ValuesWeaken : Prop := ∀ V Γ Δ σ q, Extends Γ Δ → q ∈ values V Γ σ → q ∈ values V Δ σ
end LogicLineages.PersistentMarking.DecisionPortsTargets
