module
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate
open ParametricSourceEraser ParametricLiteralWeakWrapper

def WeakAt (b : Nat) {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  ∃ k i : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν
      (constantApply (SourceAggregateCompletion.aggregate es).2) k ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν
      (identityApply (SourceAggregateCompletion.aggregate es).1) i ∧ k ≤ i

def RawUniversalWeak (b e : Nat) : Prop :=
  ∀ ν : OrdinalComponent (ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).context → Nat,
    SourceMachineRawValuations.PositiveRaw ν →
    WeakAt b (fun c => (ν c : Ordinal)) (SourceMachineAggregateBridge.sources b e)
end LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate
