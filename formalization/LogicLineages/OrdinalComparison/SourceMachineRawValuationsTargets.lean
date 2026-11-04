module
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Targets
open ExistentialPlan SourceMachineAggregateBridge

def GroundContexts : Prop :=
  (∀ (Γ : List Ty) (q : Plan Γ), AllGround Γ → AllGround (compile q).context) ∧
  (∀ b e : Nat, AllGround (compile (SourceMachineConjunctionPlan.plan b e)).context)

def PositiveCoordinateEquivalence : Prop := ∀ (Γ : List Ty), AllGround Γ →
  (∀ ρ : Variable Γ .ground → Nat, PositiveRaw (fun c => inputs ρ c+1)) ∧
  (∀ ν : OrdinalComponent Γ → Nat, PositiveRaw ν →
    ∃! ρ : Variable Γ .ground → Nat, ∀ c,ν c=inputs ρ c+1)

def RawStrictNonhalting : Prop := ∀ b e : Nat,
  (RawUniversalStrict b e ↔ UniversalStrict b e) ∧
  (RawUniversalStrict b e ↔ ¬ SourceBlankMachineSimulation.Halts e)
end LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Targets
