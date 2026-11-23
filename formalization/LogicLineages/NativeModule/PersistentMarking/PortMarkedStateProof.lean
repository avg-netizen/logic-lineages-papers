module

public import LogicLineages.NativeModule.PersistentMarking.PortLambdaStateProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceCallSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.PortMarkedStateProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse PortNormalization

theorem appendPort (S : Signature) (F : Inputs S) (Γ Δ : Context)
    (f : Head) (σ τ : Ty) (bs es : Args) (i : Nat)
    (hw : WellFormed F.data.types F.data.ports Δ) (he : Extends Γ Δ)
    (hi : Δ[i]? = some (some σ))
    (hu : Source F Γ (.marked f (.arrow σ τ) bs es)) :
    Source F Δ (.marked f τ bs (es.append (.cons (.free σ (portName F.data.names i)) .nil))) := by
  have hk := (DecisionSourceBasicProof.initial F.source F.target F.sourceType F.targetType
    F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary).1
  have hu := DecisionSourceBasicProof.weakening _ _ _ _ _ _ he hu
  have hτ : τ ∈ F.data.types := hk (.arrow σ τ)
    (DecisionSourceBasicProof.rootType _ _ _ _ _ hu) τ
    (List.mem_cons_of_mem _ (List.mem_append_right _ (DecisionSourceBasicProof.subtypeSelf τ)))
  have hv := DecisionObservedTypesProof.portUniverse F.data.types F.data.names
    F.data.sourceHeads Δ σ (.free σ (portName F.data.names i)) hk hw.2 ⟨i,hi,rfl⟩
  apply DecisionSourceConstructProof.markedBuild
  · intro υ hυ
    exact hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hυ)))
  · exact hk τ hτ
  · exact hu.2.1 f (List.mem_cons_self)
  · exact DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ hu
  · exact DecisionSourceCallSupport.appendUniverse _ _ _ _ _ _
      (DecisionSourceBasicProof.markedExtras _ _ _ _ _ _ _ _ hu) ⟨hv,True.intro⟩
end LogicLineages.PersistentMarking.PortMarkedStateProof
