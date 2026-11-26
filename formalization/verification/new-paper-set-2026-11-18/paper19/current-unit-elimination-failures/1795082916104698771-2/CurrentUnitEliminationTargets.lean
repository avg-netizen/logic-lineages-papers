module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationFiberDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence CurrentOneUnit CurrentUnitElimination

/-- Original variable identity and repeated-occurrence sharing survive
literal removal of any functional free slot. -/
def GroundProjection : Prop :=
  (∀ (Γ : List Ty) (x : Variable Γ .ground), ∃! y : Variable (groundCtx Γ) .ground, oldGround y = x) ∧
  ∀ (left right : List Ty) (σ : Ty) (hs : 0 < σ.level)
      (ρ : Variable (left ++ σ :: right) .ground → Nat)
      (x : Variable (groundCtx (left ++ right)) .ground),
    ρ (oldGround (cast (congrArg (fun Γ => Variable Γ .ground)
      (groundCtx_remove left right σ hs).symm) x)) =
      UnitObservation.remainingInputs left right σ ρ (oldGround x)

def ExactGround : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (Γ : List Ty) (τ : Ty) (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ)
      (ρ : Variable Γ .ground → Nat) (r : Nat),
        HoldsRaw p f (groundGraph p f hg a) ρ r ↔
          CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) a.term r

def ExactComposition : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    (ρ : Variable Γ .ground → Nat) (row : LinearCode) (r : Nat) (q s : OpenGraph Γ),
      (HoldsRaw p f (freeGraph row q) ρ (r+1) ↔
        ∃ l : Nat, HoldsRaw p f q ρ l ∧ holds row l 0 (r+1)) ∧
      (HoldsRaw p f (activeGraph row q s) ρ (r+1) ↔
        ∃ l l' : Nat, HoldsRaw p f q ρ l ∧ HoldsRaw p f s ρ l' ∧ holds row l l' (r+1))

def ExactClosedFiber : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (q : OpenGraph Γ)
    (hg : ∀ σ ∈ Γ, σ = .ground) (ρ : Variable Γ .ground → Nat) (n : Nat),
      (closeFiber q hg ρ n).holds p f ↔ q.holds p f ρ n

/-- Source witnesses are finite and positive. The actual renderer stores
only the quantifier-free grammar of E_src under its finite existential
natural prefix, with original ground slots and the result left free. -/
def ExactSourceGraph : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (Γ : List Ty) (τ : Ty) (a : OriginalTerm Γ τ),
      ∃ q : Tree Γ, build p (Γ.length+1) a = some q ∧
        depth q ≤ functionalCount Γ ∧ Conjunctive (render p f q).matrix ∧
        EveryScalarUnique p f q ∧
        ∀ (ρ : Variable Γ .ground → Nat),
          (∀ r : Nat, q.holds p f ρ r ↔ CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) a r) ∧
          ∃ r : Nat, 0 < r ∧ q.holds p f ρ r

def Full : Prop :=
  GroundProjection ∧ ExactGround ∧ ExactComposition ∧ ExactClosedFiber ∧ ExactSourceGraph ∧
    CurrentAbsoluteTargets.AnchorEffective

end LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationTargets
