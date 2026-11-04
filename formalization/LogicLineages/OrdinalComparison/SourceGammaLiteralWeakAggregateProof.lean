module
public import LogicLineages.OrdinalComparison.SourceGammaLiteralWeakAggregateForestProof
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Proof
open ExistentialPlan SourceMachineAggregateBridge SourceMachineRawValuations

theorem universalNonhalting : Targets.UniversalNonhalting := by
  intro b e
  have hc := SourceMachineRawValuations.Proof.positiveCoordinateEquivalence _
    (SourceMachineRawValuations.Proof.groundContexts.2 b e)
  have he : RawUniversalWeak b e ↔ RawUniversalStrict b e := by
    have hp : ∀ ν : OrdinalComponent (compile (SourceMachineConjunctionPlan.plan b e)).context → Nat,
        PositiveRaw ν → (WeakAt b (fun c => (ν c : Ordinal)) (sources b e) ↔ RawStrictAt b e ν) := by
      intro ν hn
      obtain ⟨ρ,hρ,_⟩ := hc.2 ν hn
      have hv : ν=(fun c => inputs ρ c+1) := funext hρ
      subst ν
      exact weak_iff_strict b _ _ _ (SourceMachinePlanFinite.Proof.actualGammaForest b e ρ)
    constructor
    · intro h ν hn
      exact (hp ν hn).mp (h ν hn)
    · intro h ν hn
      exact (hp ν hn).mpr (h ν hn)
  exact he.trans (SourceMachineRawValuations.Proof.rawStrictNonhalting b e).2
end LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Proof
