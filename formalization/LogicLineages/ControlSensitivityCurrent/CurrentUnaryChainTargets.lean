module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainTargets

open LogicLineages.OrdinalComparison.Source
open CurrentUnaryChain

def ActualBody : Prop :=
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (vs : List (Unary Γ)) (ws : List (OrdinalVector Γ 1)),
    Assigned p vs ws →
    AdmissibleAssignment.assignment p (SourceUnaryChain.chainBody vs) = some (fun _ => scalarSpine ws)

def ActualPartial : Prop :=
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ws : List (OrdinalVector Γ 1)),
    AdmissiblePartial.run p 0 (scalarSpine ws) = some (partialSpine p ws)

def HeadValue : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (vs : List (Unary Γ)),
    ∃ (ws : List (OrdinalVector Γ 1)) (u : OrdinalVector Γ 1),
      Assigned p vs ws ∧ AdmissibleAssignment.assignment p (SourceUnaryChain.chainSource vs) = some u ∧
      ∀ (ν : OrdinalComponent Γ → Ordinal),
        ParametricSourceSuccessor.denoteWith f ν (u 1) = headSum f ν ws

def CommonUnitValue : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (vs : List (Unary Γ)),
    ∃ (ws : List (OrdinalVector Γ 1)) (u : OrdinalVector Γ 1),
      Assigned p vs ws ∧ AdmissibleAssignment.assignment p (SourceUnaryChain.chainSource vs) = some u ∧
      ∀ (ρ : Variable Γ .ground → Nat),
        ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (u 1) =
          headSum f (commonUnits ρ) ws

def Full : Prop := ActualBody ∧ ActualPartial ∧ HeadValue ∧ CommonUnitValue

end LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainTargets
