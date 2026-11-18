module
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyLowering
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering
def numericValue (f : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat) : Expr Γ → Nat
  | .port a => a.value ρ
  | .successor a => f (a.value ρ+4)
  | .erase a b => f (3*a.value ρ+b.value ρ+8)
  | .identityZero => f 6

def SourceHolds (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat) : Prop :=
  ∀ e ∈ lower g, PolicyAddition.Equation p f (extend ρ 9 z) e.1.term e.2.term

def ForestHolds (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat) : Prop :=
  ∀ e ∈ forest g, PolicyAddition.Equation p f (extend ρ 9 z) e.1.term e.2.term

def canonicalWitness (f : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat) : Gate Γ → Fin 9 → Nat
  | .eq _ _ => ![0,0,0,0,0,0,0,0,0]
  | .add _ b _ => ![3*b.value ρ,0,0,0,0,0,0,0,0]
  | .sort a b l h =>
      let qa := f (a.value ρ+4); let qb := f (b.value ρ+4)
      let ql := f (l.value ρ+4); let qh := f (h.value ρ+4)
      let δ := max (a.value ρ) (b.value ρ)-min (a.value ρ) (b.value ρ)
      ![qa,qb,ql,qh,qa+qb,δ,3*qb,3*qh,3*δ]
  | .one a => ![2,3*a.value ρ,0,0,0,0,0,0,0]
end LogicLineages.ControlSensitivityCurrent.PolicyLowering
