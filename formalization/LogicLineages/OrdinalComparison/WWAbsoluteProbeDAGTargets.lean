module
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.Targets
open GroundEquivalence GroundClosing

def Substitution : Prop := ∀ Γ Δ τ (r : GroundMap Γ Δ) (d : Input Γ τ),
  (mapInput r d).term=d.term.substitute (GroundMap.source r) ∧ (mapInput r d).specs=d.specs

def Closing : Prop := ∀ Γ τ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (d : Input Γ τ),
  (closeInput hΓ d).term=AbsoluteObserver.close hΓ d.term ∧ (closeInput hΓ d).specs.length=d.specs.length

def Probe : Prop := ∀ Γ τ (d : Input Γ τ) (x : Variable Γ .ground),
  (probeInput d x).term=AbsoluteObserver.probe d.term x ∧ (probeInput d x).specs.length=d.specs.length+6

def Original : Prop := ∀ Γ τ (d : Input Γ τ),
  (originalInput d).term=AbsoluteObserver.originalProbe d.term ∧ (originalInput d).specs.length=d.specs.length+6

def Closed : Prop := ∀ Γ τ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (d : Input Γ τ),
  (closedInput hΓ d).term=AbsoluteObserver.closedProbe hΓ d.term ∧ (closedInput hΓ d).specs.length=d.specs.length+6
end LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.Targets
