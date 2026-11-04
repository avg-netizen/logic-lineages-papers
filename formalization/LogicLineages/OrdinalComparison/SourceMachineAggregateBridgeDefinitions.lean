module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge
open ExistentialPlan ParametricSourceEraser ParametricPrimitiveFinite

def sources (b e : Nat) :=
  (compile (SourceMachineConjunctionPlan.plan b e)).forest.map (fun f => (f.1.term,f.2.term))
def aggregate (b e : Nat) := SourceAggregateCompletion.aggregate (sources b e)

/-- Strict comparison of R with L in actual Gamma semantics, with successful
finite observations. No fallback raw scalar or fixed-Phi relation is used. -/
def StrictAt (b e : Nat)
    (ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat) : Prop :=
  ∃ l r : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ)) (aggregate b e).1 l ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) (positive (inputs ρ)) (aggregate b e).2 r ∧ r < l

def UniversalStrict (b e : Nat) : Prop := ∀ ρ, StrictAt b e ρ
end LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge
