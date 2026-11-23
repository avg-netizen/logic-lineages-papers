module

public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureTargets
public import LogicLineages.NativeModule.PersistentMarking.PortTermStateProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionClosureCallProof
open Spine NameBridge DecisionRequests PortNormalization

theorem selection (S : Signature) (F : Inputs S) (Γ f τ bs es t q i domains)
    (hs : PaperTerm S (.marked f τ bs es) τ) (ht : PaperTerm S t τ)
    (ha : At bs i q ∨ At es i q) (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (h : Invariant F (.weak Γ (.marked f τ bs es) t)) :
    Invariant F (.fullCall Γ q (ArrowPrefix domains τ) (ownerCopies f bs es domains) τ t) := by
  have hqu := ha.elim
    (fun hh => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ h.2.1) hh)
    (fun hh => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedExtras _ _ _ _ _ _ _ _ h.2.1) hh)
  have hσ := DecisionSourceBasicProof.rootType _ _ _ _ _ hqu
  rw [SpineShiftProof.annotationExact _ _ _ hq] at hσ
  have hτ := DecisionSourceBasicProof.rootType _ _ _ _ _ h.2.1
  exact ⟨h.1,hqu,
    DecisionSourceOwnerProof.ownerTuple _ _ _ _ _ _ _ _ _ _ _ (PortTermStateProof.closed S F) h.2.1 ha hq,
    h.2.2,hσ,hτ,hq,PortTermStateProof.ownerCall f bs es τ τ domains hs.1⟩

theorem result (S : Signature) (F : Inputs S) (Γ q σ args τ t r)
    (hc : apply q args = some r) (h : Invariant F (.fullCall Γ q σ args τ t)) :
    Invariant F (.weak Γ r t) := by
  obtain ⟨hw,hq,ha,ho,hσ,hτ,hqt,hat⟩ := h
  exact ⟨hw,DecisionSourceCallProof.fullCall _ _ _ _ _ _ _ _ _
    (PortTermStateProof.closed S F) hqt hat hq ha hc,ho⟩

theorem requestedTypes : DecisionClosureTargets.CallRequestedTypes := by
  intro S F Γ q σ args τ t h
  exact ⟨PortTermStateProof.closed S F σ h.2.2.2.2.1,
    PortTermStateProof.closed S F τ h.2.2.2.2.2.1⟩
end LogicLineages.PersistentMarking.DecisionClosureCallProof
