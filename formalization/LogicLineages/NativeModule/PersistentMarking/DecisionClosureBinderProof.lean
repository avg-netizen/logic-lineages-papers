module

public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureTargets
public import LogicLineages.NativeModule.PersistentMarking.PortMarkedStateProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionClosureBinderProof
open Spine NameBridge DecisionPorts ObservationLambda DecisionRequests PortNormalization

theorem absChild (S : Signature) (F : Inputs S) (Γ σ τ s t i)
    (hs : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ)) (hi : firstUnused Γ = some i)
    (h : Invariant F (.weak Γ (.lam σ s) (.lam σ t))) :
    Invariant F (.weak (fillSlot Γ i σ) (openBody σ (portName F.data.names i) s)
      (openBody σ (portName F.data.names i) t)) := by
  obtain ⟨j,hj,hσ,hw,he,ho⟩ := PortLambdaStateProof.descent S F Γ σ t h.1 h.2.2
  have hij : i = j := Option.some.inj (hi.symm.trans hj)
  subst j
  have hlu := ObservationPortUpdateProof.firstSound Γ i hi
  have hl := (ObservationPortUpdateProof.fillExact Γ i σ hlu).2.2.1
  exact ⟨hw,PortLambdaStateProof.sourceOpening S F Γ _ σ τ s i hw he hl hs.1 h.2.1,ho⟩

theorem fabsChild (S : Signature) (F : Inputs S) (Γ σ τ f bs es t i)
    (hs : PaperTerm S (.marked f (.arrow σ τ) bs es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ)) (hi : firstUnused Γ = some i)
    (h : Invariant F (.weak Γ (.marked f (.arrow σ τ) bs es) (.lam σ t))) :
    Invariant F (.weak (fillSlot Γ i σ)
      (.marked f τ bs (es.append (.cons (.free σ (portName F.data.names i)) .nil)))
      (openBody σ (portName F.data.names i) t)) := by
  obtain ⟨j,hj,hσ,hw,he,ho⟩ := PortLambdaStateProof.descent S F Γ σ t h.1 h.2.2
  have hij : i = j := Option.some.inj (hi.symm.trans hj)
  subst j
  have hlu := ObservationPortUpdateProof.firstSound Γ i hi
  have hl := (ObservationPortUpdateProof.fillExact Γ i σ hlu).2.2.1
  exact ⟨hw,PortMarkedStateProof.appendPort S F Γ _ f σ τ bs es i hw he hl h.2.1,ho⟩
end LogicLineages.PersistentMarking.DecisionClosureBinderProof
