import LogicLineages.PersistentMarking.DecisionClosureBinderProof
import LogicLineages.PersistentMarking.DecisionClosureCallProof
import LogicLineages.PersistentMarking.PortListCasesProof
import LogicLineages.PersistentMarking.PortHeadObservationProof
namespace LogicLineages.PersistentMarking.DecisionClosureStepProof
open Spine NameBridge DecisionRequests PortNormalization

theorem step : DecisionClosureTargets.ChildPreservation := by
  intro S F parent child edge h
  cases edge with
  | abs hs ht hi => exact DecisionClosureBinderProof.absChild S F _ _ _ _ _ _ hs ht hi h
  | funHead hs ht he hty => exact ⟨h.1,DecisionSourceBasicProof.headBase _ _ _ _ _ _ h.2.1,
      PortHeadObservationProof.headObservations S F _ _ _ h.1 h.2.2⟩
  | put hs ht => exact ⟨h.1,DecisionSourceMarkProof.sourceMark _ _ _ _ _ _ h.2.1 rfl,h.2.2⟩
  | select hs ht ha hq => exact DecisionClosureCallProof.selection S F _ _ _ _ _ _ _ _ _ hs ht ha hq h
  | callResult hc => exact DecisionClosureCallProof.result S F _ _ _ _ _ _ _ hc h
  | fabs hs ht hi => exact DecisionClosureBinderProof.fabsChild S F _ _ _ _ _ _ _ _ hs ht hi h
  | copy hs ht hp => exact ⟨h.1,PortTermStateProof.owner S F _ _ _ _ _ h.2.1,
      PortHeadObservationProof.headObservations S F _ _ _ h.1 h.2.2⟩
  | statBase hs ht he => exact ⟨h.1,DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ h.2.1,
      PortHeadObservationProof.headObservations S F _ _ _ h.1 h.2.2⟩
  | statWhole hs ht he => exact ⟨h.1,PortTermStateProof.owner S F _ _ _ _ _ h.2.1,
      PortHeadObservationProof.headObservations S F _ _ _ h.1 h.2.2⟩
  | strict hs ht hm => exact ⟨h.1,DecisionSourceMarkProof.sourceMark _ _ _ _ _ _ h.2.1 hm,h.2.2⟩
  | matchingHead hr => exact ⟨h.1,h.2.1.1,(PortListStateProof.observedRemove S F _ hr h.2.2).1⟩
  | matchingTail hr => exact ⟨h.1,h.2.1.2,(PortListStateProof.observedRemove S F _ hr h.2.2).2⟩
  | multisetMatch hs ht hn => exact ⟨h.1,(PortListStateProof.sourcesSplit S F _ hs h.2.1).1,
      (PortListStateProof.observedSplit S F _ ht h.2.2).1⟩
  | multisetCover hs ht hn => exact ⟨h.1,(PortListStateProof.sourcesSplit S F _ hs h.2.1).2,
      (PortListStateProof.observedSplit S F _ ht h.2.2).2⟩
  | coverageHead ha => exact ⟨h.1,DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _ h.2.1 ha,
      (PortListStateProof.observedCons S F _ _ _ h.2.2).1⟩
  | coverageTail ha => exact ⟨h.1,h.2.1,(PortListStateProof.observedCons S F _ _ _ h.2.2).2⟩
  | wholeHead =>
    have hq := (PortListStateProof.observedCons S F _ _ _ h.2.2).1
    have hK := DecisionSourceBasicProof.rootType _ _ _ _ _ (PortStateProof.observedUniverse S F _ _ h.1 hq)
    exact ⟨h.1,h.2.1 _ hK,hq⟩
  | wholeTail => exact ⟨h.1,h.2.1,(PortListStateProof.observedCons S F _ _ _ h.2.2).2⟩
end LogicLineages.PersistentMarking.DecisionClosureStepProof
