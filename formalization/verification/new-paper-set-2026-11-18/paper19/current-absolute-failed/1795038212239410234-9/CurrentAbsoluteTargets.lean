module
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence CurrentAbsolute

def AnchorExact : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (Γ : List Ty) (τ : Ty) (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ),
      0 < anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩) ∧
      Scalar p f (fun _ => 0) (AbsoluteObserver.close hg d.term)
        (anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩))

def AnchorEffective : Prop :=
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    ∀ (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
      Computable (anchor p f)

def ProbeIdentity : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (Γ : List Ty) (τ : Ty) (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ)
      (ρ : OrdinalComponent Γ → Nat) (v x y : Nat), Scalar p f ρ d.term v →
      let σ := AbsoluteObserver.extend ρ x y
      (PolicyCollision.rawScalar p f σ (AbsoluteProbeDAG.originalInput d).term =
        PolicyCollision.rawScalar p f σ (AbsoluteProbeDAG.closedInput hg d).term ↔
      AbsoluteObserver.factor τ * v + (x+1) = AbsoluteObserver.factor τ *
        anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩) + (y+1))

def FormulaExact : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (Γ : List Ty) (τ : Ty) (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ)
      (ρ : OrdinalComponent Γ → Nat) (v : Nat),
      Formula p f hg d ρ v ↔ Scalar p f ρ d.term v

def Full : Prop := AnchorExact ∧ AnchorEffective ∧ ProbeIdentity ∧ FormulaExact

end LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteTargets
