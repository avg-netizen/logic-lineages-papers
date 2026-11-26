module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineDecisionLogicProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyThinChecks
public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureInitialProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineDecisionSplitChecks
open Spine DecisionRequests PortNormalization
open ProtectedSpineDecisionTargets ProtectedSpineDecisionLogicProof

theorem exact_Decidability : Decidability :=
  correctOfSameType fun S s t σ hS hOrdS hT hOrdT => by
    let F : Inputs S := ⟨s,t,σ,σ,hS,hT,hOrdS,hOrdT⟩
    let Γ := blank F.data.ports
    have hRoot := (DecisionClosureInitialProof.initial S F).1
    have hAdequacy := ProtectedSpineAdequacyThinChecks.exact_ExactObservation S F Γ s t σ
      hRoot.1 hRoot.2.1 hRoot.2.2 hS hT
    exact liftRoot S F (sameType S s t σ hS hT) hAdequacy

#print axioms exact_Decidability
end LogicLineages.PersistentMarking.ProtectedSpineDecisionSplitChecks
