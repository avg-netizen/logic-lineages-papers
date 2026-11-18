import LogicLineages.PersistentMarking.PortRenameProof
import LogicLineages.PersistentMarking.PortLambdaStateProof
namespace LogicLineages.PersistentMarking.PortAbsProof
open Spine NameBridge DecisionPorts ObservationLambda PortNormalization RefinementRenamingTargets RefinementRenameSupport

theorem absCase (S : Signature) (F : Inputs S) (σ τ : Ty) (x : Nat) (s t : Expr)
    (hs : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false) (hxt : freeOccurs (σ,x) t = false)
    (ih : WeakMotive F (openBody σ x s) (openBody σ x t)) :
    WeakMotive F (.lam σ s) (.lam σ t) := by
  intro π Γ hp hw hu ho
  have hsp := paper S π _ _ hs
  have htp := paper S π _ _ ht
  simp only [renameLam] at hu ho hsp htp ⊢
  obtain ⟨i,hi,hσ,hwi,he,hot⟩ := PortLambdaStateProof.descent S F Γ σ (rename π t) hw ho
  have hlookup := ObservationPortUpdateProof.firstSound Γ i hi
  have hys : freeOccurs (σ,portName F.data.names i) (rename π s) = false :=
    PortStateProof.unusedAbsent _ _ _ _ (.lam σ (rename π s)) i σ hu hlookup
  have hyt : freeOccurs (σ,portName F.data.names i) (rename π t) = false :=
    PortStateProof.unusedAbsent _ _ _ _ (.lam σ (rename π t)) i σ
      (PortStateProof.observedUniverse S F Γ _ hw ho) hlookup
  have hpxs : freeOccurs (σ,π σ x) (rename π s) = false := by rw [occurs π hp,hxs]
  have hpxt : freeOccurs (σ,π σ x) (rename π t) = false := by rw [occurs π hp,hxt]
  have hfill := (ObservationPortUpdateProof.fillExact Γ i σ hlookup).2.2.1
  have hus := PortLambdaStateProof.sourceOpening S F Γ (fillSlot Γ i σ) σ τ
    (rename π s) i hwi he hfill hsp.1 hu
  have hchild := ih (PortRenameProof.adjusted π σ x (portName F.data.names i))
    (fillSlot Γ i σ) (PortRenameProof.adjustedInjective π σ x _ hp) hwi
  rw [PortRenameProof.adjustedOpening π σ x _ s hpxs hys,
      PortRenameProof.adjustedOpening π σ x _ t hpxt hyt] at hchild
  exact .abs hsp htp hσ hi hys hyt (hchild hus hot)
end LogicLineages.PersistentMarking.PortAbsProof
