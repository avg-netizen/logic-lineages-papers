import LogicLineages.PersistentMarking.DecisionClosureInitialProof
import LogicLineages.PersistentMarking.DecisionClosureStepProof
namespace LogicLineages.PersistentMarking.DecisionClosureProof
open Spine NameBridge DecisionRequests PortNormalization

theorem reachable (S : Signature) (F : Inputs S) (root request : Request)
    (hr : Invariant F root) (h : Reach S F.data.types F.data.names root request) : Invariant F request := by
  induction h with
  | root => exact hr
  | step path edge ih => exact DecisionClosureStepProof.step S F _ _ edge ih

theorem full : DecisionClosureTargets.FullClosure := by
  intro S F
  obtain ⟨hw,hs⟩ := DecisionClosureInitialProof.equivalence S F
  obtain ⟨hiw,his⟩ := DecisionClosureInitialProof.initial S F
  refine ⟨hw,hs,fun r h => reachable S F _ r hiw h,fun r h => reachable S F _ r his h,?_⟩
  intro Γ q σ args τ t h
  exact DecisionClosureCallProof.requestedTypes S F Γ q σ args τ t (reachable S F _ _ hiw h)
end LogicLineages.PersistentMarking.DecisionClosureProof
