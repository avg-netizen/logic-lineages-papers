import LogicLineages.PersistentMarking.MarkedConstructorEncodingProof

namespace LogicLineages.PersistentMarking.MarkedConstructorEndomapProof
open Spine FiniteDomainSchema HereditaryDomainCode
open MarkedConstructorOperator
open MarkedConstructorTargets (PrefixClosed)

theorem endomap (S : Signature) (E : Environment) (heads : List Head) (hc : PrefixClosed E) :
    MarkedConstructorOperatorTargets.Endomap S E heads := by
  intro M hm
  have hv : MarkedFamilyCoherence.ValidFamily E heads (nextFamily S E heads M) :=
    ⟨fun p hp => (MarkedConstructorEncodingProof.encodeAt S E heads M p hc hm hp).1,
      MarkedConstructorEncodingProof.nextInputOrder S E heads M hc hm,
      MarkedConstructorEncodingProof.nextCoherent S E heads M hc hm⟩
  obtain ⟨N,hN,hn,hdecode⟩ := MarkedFamilyRetentionProof.encodingComplete E heads _ hv
  have he : step S E heads M = N := by simp [step,hN]
  rw [he]
  refine ⟨hN,hn,?_⟩
  intro p hp
  rw [hdecode p hp]
  exact (MarkedConstructorEncodingProof.encodeAt S E heads M p hc hm hp).2

theorem monotone (S : Signature) (E : Environment) (heads : List Head) (hc : PrefixClosed E) :
    MarkedConstructorOperatorTargets.Monotone S E heads := by
  intro M N hm hn hmn
  have hM := endomap S E heads hc M hm
  have hN := endomap S E heads hc N hn
  apply (MarkedFamilyOrderProof.orderExact E heads _ _ hM.2.1 hN.2.1).mpr
  intro p hp
  have hmc := ((MarkedFamilyRetentionProof.retentionExact E heads _).mp hM.2.1).2.1 p hp
  have hnc := ((MarkedFamilyRetentionProof.retentionExact E heads _).mp hN.2.1).2.1 p hp
  have hsem := MarkedConstructorFamilyOrderProof.familyMonotone S E heads M N p hc hm hn hp hmn
  exact (HereditaryCodeOrderProof.exactOrder E p.2.1 p.2.2.1 _ _ hp.2.2.1 hmc hnc).mpr
    (HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm (hM.2.2 p hp))
      (HereditaryValueEqualityProof.symm (hN.2.2 p hp)) hsem)

end LogicLineages.PersistentMarking.MarkedConstructorEndomapProof
