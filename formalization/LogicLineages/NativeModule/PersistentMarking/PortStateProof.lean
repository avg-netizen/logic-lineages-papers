module

public import LogicLineages.NativeModule.PersistentMarking.PortNormalizationTargets
public import LogicLineages.NativeModule.PersistentMarking.DecisionObservedTypesProof

@[expose] public section

namespace LogicLineages.PersistentMarking.PortStateProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse PortNormalization DecisionSourceBasicProof

theorem observedUniverse : PortNormalizationTargets.ObservedUniverse := by
  intro S F Γ q hw hobs
  have hk : Closed F.data.types := (initial F.source F.target F.sourceType F.targetType F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary).1
  have htu : Universe F.data.types F.data.names (heads F.target) Γ F.target := by
    refine ⟨?_,fun _ h => h,?_⟩
    · intro α hα
      exact List.mem_append_right _ ((DecisionInventoryProof.ordinaryExact EmptyContext F.target F.targetType F.targetPaper.1 F.targetOrdinary α).mp hα)
    · intro n hn
      exact Or.inl (List.mem_append_right _ ((DecisionInventoryProof.freeExact F.target n).mpr hn))
  obtain ⟨stack,r,vs,hocc,hvs,hqtype,hdepth,heq⟩ :=
    (DecisionObservationProof.enumeration F.data.names F.data.ports Γ F.target q.type q).mp hobs
  subst q
  have hru := occurrence F.data.types F.data.names (heads F.target) Γ [] F.target stack r htu hocc
  have hrt := DecisionOccurrenceProof.typed [] F.target F.targetType stack r F.targetPaper.1 hocc
  have hvu := DecisionObservedTypesProof.assignmentUniverse F.data.types F.data.names (heads F.target) Γ stack vs hk hw.2 hvs
  exact DecisionSourceSubstitutionProof.boundSubstitution F.data.types F.data.names (heads F.target) Γ stack vs r r.type
    hrt (DecisionAssignmentProof.typed F.data.names Γ stack vs hvs) hru hvu

theorem unusedAbsent : PortNormalizationTargets.UnusedAbsent := by
  intro K V H Γ q i σ hu hi
  cases hn : freeOccurs (σ,portName V i) q with
  | false => rfl
  | true =>
    rcases hu.2.2 (σ,portName V i) hn with hv|hp
    · exact False.elim (DecisionPortsProof.fresh V i σ hv)
    · obtain ⟨j,hj,hq⟩ := hp
      have he : portName V i = portName V j := (Expr.free.inj hq).2
      have hij := DecisionPortsProof.injective V i j he
      subst j; rw [hi] at hj; cases hj
end LogicLineages.PersistentMarking.PortStateProof
