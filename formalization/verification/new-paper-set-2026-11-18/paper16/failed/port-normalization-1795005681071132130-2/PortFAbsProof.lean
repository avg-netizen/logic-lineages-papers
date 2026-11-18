import LogicLineages.PersistentMarking.PortAbsProof
import LogicLineages.PersistentMarking.PortMarkedStateProof
import LogicLineages.PersistentMarking.ExtendedRenameSupport
namespace LogicLineages.PersistentMarking.PortFAbsProof
open Spine NameBridge DecisionPorts ObservationLambda PortNormalization RefinementRenamingTargets RefinementRenameSupport

theorem fabsCase (S : Signature) (F : Inputs S) (σ τ : Ty) (x : Nat)
    (f : Head) (ss es : Args) (t : Expr)
    (hs : PaperTerm S (.marked f (.arrow σ τ) ss es) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) (.marked f (.arrow σ τ) ss es) = false)
    (hxt : freeOccurs (σ,x) t = false)
    (ih : WeakMotive F (.marked f τ ss (es.append (.cons (.free σ x) .nil))) (openBody σ x t)) :
    WeakMotive F (.marked f (.arrow σ τ) ss es) (.lam σ t) := by
  intro π Γ hp hw hu ho
  have hsp := paper S π _ _ hs
  have htp := paper S π _ _ ht
  simp only [renameLam,renameMarked] at hu ho hsp htp ⊢
  obtain ⟨i,hi,hσ,hwi,he,hot⟩ := PortLambdaStateProof.descent S F Γ σ (rename π t) hw ho
  have hlookup := ObservationPortUpdateProof.firstSound Γ i hi
  have hys : freeOccurs (σ,portName F.data.names i) (rename π (.marked f (.arrow σ τ) ss es)) = false :=
    PortStateProof.unusedAbsent _ _ _ _ _ i σ hu hlookup
  have hyt : freeOccurs (σ,portName F.data.names i) (rename π t) = false :=
    PortStateProof.unusedAbsent _ _ _ _ (.lam σ (rename π t)) i σ
      (PortStateProof.observedUniverse S F Γ _ hw ho) hlookup
  have hpxs : freeOccurs (σ,π σ x) (rename π (.marked f (.arrow σ τ) ss es)) = false := by rw [occurs π hp,hxs]
  have hpxt : freeOccurs (σ,π σ x) (rename π t) = false := by rw [occurs π hp,hxt]
  have hparent := PortRenameProof.adjustedParent π σ x (portName F.data.names i) _ hpxs hys
  simp only [renameMarked] at hparent
  have hbs := (Expr.marked.inj hparent).2.2.1
  have hes := (Expr.marked.inj hparent).2.2.2
  have hfill := (ObservationPortUpdateProof.fillExact Γ i σ hlookup).2.2.1
  have hus := PortMarkedStateProof.appendPort S F Γ (fillSlot Γ i σ) f σ τ
    (renameArgs π ss) (renameArgs π es) i hwi he hfill hu
  have hchild := ih (PortRenameProof.adjusted π σ x (portName F.data.names i))
    (fillSlot Γ i σ) (PortRenameProof.adjustedInjective π σ x _ hp) hwi
  rw [PortRenameProof.adjustedOpening π σ x _ t hpxt hyt] at hchild
  simp only [renameMarked,ExtendedRenameSupport.append,renameCons,renameNil,renameFree,hbs,hes,
    PortRenameProof.adjusted,PortRenameProof.compose,RefinementOpeningProof.swapName] at hchild
  exact .fabs hsp htp hσ hi hys hyt (hchild hus hot)
end LogicLineages.PersistentMarking.PortFAbsProof
