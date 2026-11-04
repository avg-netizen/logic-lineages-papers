module
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionAdequacyProof
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof
open SourceMachineAggregateBridge

theorem exactNonhalting : Targets.ExactNonhalting := by
  intro b e
  unfold SourceMachineQueryCode.output
  rw [(SourceMachineQueryCode.Proof.exactPackaging.2 b e).1]
  rw [canonicalQueryAdequacy _ _ (SourceMachineRawValuations.Proof.groundContexts.2 b e)]
  have hs : Strict (SourceMachineControlNonperiodicity.gamma b) (aggregate b e).2 (aggregate b e).1 ↔
      SourceMachineRawValuations.RawUniversalStrict b e := by
    constructor
    · intro h ν hp
      rcases h ν hp with ⟨x,y,hx,hy,hlt⟩
      exact ⟨y,x,hy,hx,hlt⟩
    · intro h ν hp
      rcases h ν hp with ⟨l,r,hl,hr,hlt⟩
      exact ⟨r,l,hr,hl,hlt⟩
  exact hs.trans (SourceMachineRawValuations.Proof.rawStrictNonhalting b e).2
end LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof
