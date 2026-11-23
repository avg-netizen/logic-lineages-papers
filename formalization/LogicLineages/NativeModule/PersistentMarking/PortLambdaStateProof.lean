module

public import LogicLineages.NativeModule.PersistentMarking.PortStateProof
public import LogicLineages.NativeModule.PersistentMarking.ObservationLambdaProof
public import LogicLineages.NativeModule.PersistentMarking.ElementarySupportProof

@[expose] public section

namespace LogicLineages.PersistentMarking.PortLambdaStateProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionObservations ObservationLambda PortNormalization

theorem descent (S : Signature) (F : Inputs S) (Γ : Context) (σ : Ty) (body : Expr)
    (hw : WellFormed F.data.types F.data.ports Γ) (ho : Observed F Γ (.lam σ body)) :
    ∃ i, firstUnused Γ = some i ∧ σ ∈ F.data.types ∧
      WellFormed F.data.types F.data.ports (fillSlot Γ i σ) ∧
      Extends Γ (fillSlot Γ i σ) ∧
      Observed F (fillSlot Γ i σ) (openBody σ (portName F.data.names i) body) := by
  have hu := PortStateProof.observedUniverse S F Γ (.lam σ body) hw ho
  have hs : σ ∈ F.data.types := hu.1 σ
    (List.mem_append_left _ (List.mem_append_right _ (DecisionSourceBasicProof.subtypeSelf σ)))
  obtain ⟨i,hi,hwi,he,hn,hobs⟩ := ObservationLambdaProof.descent S F.data.types
    F.data.names F.data.ports Γ F.target F.targetType σ body.type body
    F.targetPaper F.targetOrdinary hw hs ho
  have hpaper := (DecisionObservationProof.paper S F.data.names F.data.ports Γ F.target
    F.targetType (.arrow σ body.type) (.lam σ body) F.targetPaper F.targetOrdinary ho).1
  have hopen := ElementarySupportProof.openingPaper S σ body.type (portName F.data.names i) body hpaper
  have htype := SpineShiftProof.annotationExact _ _ _ hopen.1
  refine ⟨i,hi,hs,hwi,he,?_⟩
  unfold Observed
  rw [htype]
  exact hobs

theorem sourceOpening (S : Signature) (F : Inputs S) (Γ Δ : Context)
    (σ τ : Ty) (body : Expr) (i : Nat)
    (hw : WellFormed F.data.types F.data.ports Δ) (he : Extends Γ Δ)
    (hi : Δ[i]? = some (some σ))
    (ht : Typed EmptyContext (.lam σ body) (.arrow σ τ))
    (hu : Source F Γ (.lam σ body)) :
    Source F Δ (openBody σ (portName F.data.names i) body) := by
  have hk := (DecisionSourceBasicProof.initial F.source F.target F.sourceType F.targetType
    F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary).1
  have hb := DecisionSourceBasicProof.lamChild _ _ _ _ _ _ hu
  have hbu := DecisionSourceBasicProof.weakening _ _ _ _ _ _ he hb
  have hv := DecisionObservedTypesProof.portUniverse F.data.types F.data.names
    F.data.sourceHeads Δ σ (.free σ (portName F.data.names i)) hk hw.2 ⟨i,hi,rfl⟩
  cases ht with
  | lam hb =>
    exact DecisionSourceSubstitutionProof.boundSubstitution F.data.types F.data.names
      F.data.sourceHeads Δ [σ] (.cons (.free σ (portName F.data.names i)) .nil)
      body τ hb (.cons .free .nil) hbu ⟨hv,True.intro⟩
end LogicLineages.PersistentMarking.PortLambdaStateProof
