module
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenDefinitions
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanPlan
open PrimitiveLowering ExistentialPlan

/-- A literal finite conjunction of the accepted concrete primitive gates. -/
def gates {Γ} (gs : List (Gate Γ)) : Plan Γ := gs.foldr Plan.gate .done

/-- Existentially bind the actual finite fresh ground prefix, leaving every
old context coordinate in place. No semantic predicate is embedded as syntax. -/
def bindBlock {Γ} : (n : Nat) → Plan (List.replicate n Ty.ground ++ Γ) → Plan Γ
  | 0, q => q
  | n+1, q => bindBlock n (.existsGround q)

/-- Explicit natural valuation of the fresh prefix. -/
def block {Γ} (ρ : Variable Γ .ground → Nat) :
    (n : Nat) → (Fin n → Nat) → Variable (List.replicate n Ty.ground++Γ) .ground → Nat
  | 0, _ => ρ
  | n+1, v => ExistentialPlan.extend (block ρ n (fun i => v i.succ)) (v 0)

/-- The complete finite Boolean matrix, not yet the arbitrary arithmetic or
supplied-source front end: bind all globally shared Boolean witness wires. -/
def matrixPlan {Γ n m} (d : BooleanWire.Dag n m) (a : Fin n → Port Γ) (root : Fin m) : Plan Γ :=
  bindBlock (9*m+1) (gates (BooleanFlatten.compile d a root))
end LogicLineages.OrdinalComparison.Source.BooleanPlan
