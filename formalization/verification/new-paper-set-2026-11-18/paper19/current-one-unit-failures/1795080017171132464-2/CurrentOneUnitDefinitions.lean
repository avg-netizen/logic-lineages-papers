module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteDefinitions
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence
open AdmissibleAssignment (assignment repeated)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual d, d', and whole-free flag, before any value collection. -/
abbrev Coefficients := Nat × Nat × Bool

/-- A finite addition equation α L + β = γ L' + δ R + ε.
Each number is a compile-time finite numeral coefficient/constant. -/
abbrev LinearCode := Nat × Nat × Nat × Nat × Nat

def equation (level : Nat) (data : Coefficients) : LinearCode :=
  let d := data.1
  let d' := data.2.1
  let k := 2*(level+1)
  let p₀ := k+1
  let c := 4*k*d'+k
  if data.2.2 then (1,0,0,d+1,d)
  else (p₀*d',d*c,d,p₀*(d'-d),0)

def holds (code : LinearCode) (l l' r : Nat) : Prop :=
  code.1*l + code.2.1 = code.2.2.1*l' + code.2.2.2.1*r + code.2.2.2.2

/-- Actual selected-policy literal unused-binder repetition and retention
of the original scalar before any subsequent size or partial. -/
def inflated {Γ : List Ty} (p : AdmissibleSum.Policy) (τ : Ty)
    (e : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (repeated p .scalarRepeat (OneUnit.copies τ) (.add e .one)) e

def typedCoefficients (p : AdmissibleSum.Policy) {Γ : List Ty} {σ τ : Ty}
    (a : OriginalTerm (σ :: Γ) τ) : Option Coefficients := do
  let h ← assignment p a
  let v ← assignment p (OneUnit.unused a)
  return (OneUnit.multiplier h,OneUnit.multiplier v,ordinalHeadFree (h 0))

/-- Input wires for the selected head: F's entire actual assignment is
observed at unit; other functional names retain their common units, and
all remaining ground coordinates come from the genuine same old wires. -/
def headUnitWires {Γ : List Ty} {σ : Ty} (ρ : Variable Γ .ground → Nat) :
    OrdinalComponent (σ :: Γ) → Nat
  | ⟨_,.here,_⟩ => 0
  | ⟨τ,.there x,j⟩ => ExistentialPlan.inputs ρ ⟨τ,x,j⟩

/-- The literal finite positive-coefficient graph, using the two actual
typed source observations (only the first when the original scalar is
whole-free). These scalar values are the raw positive observed naturals. -/
def Formula (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} {σ τ : Ty}
    (ρ : Variable Γ .ground → Nat) (a : OriginalTerm (σ :: Γ) τ)
    (d : Coefficients) (r : Nat) : Prop :=
  if d.2.2 then
    ∃ l : Nat, CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.first a) l ∧
      holds (equation τ.level d) l 0 r
  else
    ∃ l l' : Nat, CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.first a) l ∧
      CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.second a) l' ∧
      holds (equation τ.level d) l l' r

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
