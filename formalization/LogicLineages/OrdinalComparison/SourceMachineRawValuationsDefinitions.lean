module
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations
open ExistentialPlan ParametricSourceEraser SourceMachineAggregateBridge

def AllGround (Γ : List Ty) : Prop := ∀ σ ∈ Γ, σ=Ty.ground
def PositiveRaw {Γ} (ν : OrdinalComponent Γ → Nat) : Prop := ∀ c,0 < ν c

def RawStrictAt (b e : Nat)
    (ν : OrdinalComponent (compile (SourceMachineConjunctionPlan.plan b e)).context → Nat) : Prop :=
  ∃ l r : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (ν c : Ordinal)) (aggregate b e).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (ν c : Ordinal)) (aggregate b e).2 r ∧ r < l

def RawUniversalStrict (b e : Nat) : Prop := ∀ ν, PositiveRaw ν → RawStrictAt b e ν
end LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations
