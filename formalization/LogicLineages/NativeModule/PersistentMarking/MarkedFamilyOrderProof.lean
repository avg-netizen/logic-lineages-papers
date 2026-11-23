module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyLatticeTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyRetentionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem orderExact : MarkedFamilyLatticeTargets.OrderExact := by
  intro E heads a b ha hb
  have hfa := ((MarkedFamilyRetentionProof.retentionExact E heads a).mp ha).1
  have hfb := ((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).1
  unfold MarkedFamilyLattice.le
  simp only [List.all_eq_true]
  constructor
  · intro h p hp
    have hh := h p ((MarkedFamilyParameterProof.enumeration E heads p).mpr hp)
    simpa only [MarkedFamilyFilterProof.outputDecode E heads a p hfa hp,
      MarkedFamilyFilterProof.outputDecode E heads b p hfb hp] using hh
  · intro h p hp
    have hv := (MarkedFamilyParameterProof.enumeration E heads p).mp hp
    simpa only [MarkedFamilyFilterProof.outputDecode E heads a p hfa hv,
      MarkedFamilyFilterProof.outputDecode E heads b p hfb hv] using h p hv

theorem partialOrder : MarkedFamilyLatticeTargets.PartialOrder := by
  intro E heads
  refine ⟨?_,?_,?_⟩
  · intro a ha
    apply (orderExact E heads a a ha ha).mpr
    intro p hp
    have hv := ((MarkedFamilyRetentionProof.retentionExact E heads a).mp ha).2.1 p hp
    exact (HereditaryPartialOrderProof.partialOrder E p.2.1 p.2.2.1 hp.2.2.1).1 _ hv
  · intro a b c ha hb hc hab hbc
    apply (orderExact E heads a c ha hc).mpr
    intro p hp
    have hpa := ((MarkedFamilyRetentionProof.retentionExact E heads a).mp ha).2.1 p hp
    have hpb := ((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).2.1 p hp
    have hpc := ((MarkedFamilyRetentionProof.retentionExact E heads c).mp hc).2.1 p hp
    exact (HereditaryPartialOrderProof.partialOrder E p.2.1 p.2.2.1 hp.2.2.1).2.1 _ _ _ hpa hpb hpc
      ((orderExact E heads a b ha hb).mp hab p hp) ((orderExact E heads b c hb hc).mp hbc p hp)
  · intro a b ha hb hab hba
    have hfa := ((MarkedFamilyRetentionProof.retentionExact E heads a).mp ha).1
    have hfb := ((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).1
    have he : FamilyEq E heads (MarkedFamilyCoding.decode E heads a) (MarkedFamilyCoding.decode E heads b) := by
      intro p hp
      have hpa := ((MarkedFamilyRetentionProof.retentionExact E heads a).mp ha).2.1 p hp
      have hpb := ((MarkedFamilyRetentionProof.retentionExact E heads b).mp hb).2.1 p hp
      exact (HereditaryPartialOrderProof.partialOrder E p.2.1 p.2.2.1 hp.2.2.1).2.2 _ _ hpa hpb
        ((orderExact E heads a b ha hb).mp hab p hp) ((orderExact E heads b a hb ha).mp hba p hp)
    have hh := MarkedFamilyEncodingProof.encodingCongruence E heads _ _ he
    rw [MarkedFamilyRoundtripProof.codeRoundtrip E heads a hfa,
      MarkedFamilyRoundtripProof.codeRoundtrip E heads b hfb] at hh
    exact Option.some.inj hh
end LogicLineages.PersistentMarking.MarkedFamilyOrderProof
