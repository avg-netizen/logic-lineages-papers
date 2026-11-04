module
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsCoordinatesProof
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Proof
open ExistentialPlan SourceMachineAggregateBridge

theorem rawStrictNonhalting : Targets.RawStrictNonhalting := by
  intro b e
  have hc := positiveCoordinateEquivalence _ (groundContexts.2 b e)
  have he : RawUniversalStrict b e ↔ UniversalStrict b e := by
    constructor
    · intro h ρ
      exact h (fun c => inputs ρ c+1) (hc.1 ρ)
    · intro h ν hp
      obtain ⟨ρ,hρ,_⟩ := hc.2 ν hp
      have hv : ν=(fun c => inputs ρ c+1) := funext hρ
      subst ν
      exact h ρ
  exact ⟨he,he.trans (SourceMachineAggregateBridge.Proof.universalStrictNonhalting b e)⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineRawValuations.Proof
