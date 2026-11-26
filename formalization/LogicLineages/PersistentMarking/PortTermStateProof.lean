import LogicLineages.PersistentMarking.PortStateProof
import LogicLineages.PersistentMarking.DecisionSourceMarkProof
import LogicLineages.PersistentMarking.DecisionSourceOwnerProof
import LogicLineages.PersistentMarking.DecisionSourceCallProof
namespace LogicLineages.PersistentMarking.PortTermStateProof
open Spine NameBridge DecisionSourceUniverse PortNormalization

theorem closed (S : Signature) (F : Inputs S) : DecisionSourceUniverse.Closed F.data.types :=
  (DecisionSourceBasicProof.initial F.source F.target F.sourceType F.targetType
    F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary).1

theorem owner (S : Signature) (F : Inputs S) (Γ f τ bs es)
    (hu : Source F Γ (.marked f τ bs es)) : OwnerSource F Γ f bs es := by
  intro υ hυ
  exact DecisionSourceMarkProof.sourceRetype _ _ _ _ f υ τ bs es (closed S F) hu hυ

theorem ownerCall (f : Head) (bs es : Args) (σ τ : Ty) (domains : List Ty)
    (ht : Typed EmptyContext (.marked f σ bs es) σ) :
    CallTyped EmptyContext (ArrowPrefix domains τ) (ownerCopies f bs es domains) τ := by
  cases ht with
  | marked hb he =>
    induction domains with
    | nil => exact .nil
    | cons δ domains ih => exact .cons (.marked hb he) ih

theorem selected (S : Signature) (F : Inputs S) (Γ f τ bs es domains q i r)
    (hp : PaperTerm S (.marked f τ bs es) τ)
    (hu : Source F Γ (.marked f τ bs es))
    (ha : At bs i q ∨ At es i q) (ht : Typed EmptyContext q (ArrowPrefix domains τ))
    (hc : apply q (ownerCopies f bs es domains) = some r) : Source F Γ r := by
  have hqu := ha.elim
    (fun h => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ hu) h)
    (fun h => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedExtras _ _ _ _ _ _ _ _ hu) h)
  have hv := DecisionSourceOwnerProof.ownerTuple _ _ _ _ _ _ _ _ _ _ _ (closed S F) hu ha ht
  exact DecisionSourceCallProof.fullCall _ _ _ _ _ _ _ _ _ (closed S F) ht
    (ownerCall f bs es τ τ domains hp.1) hqu hv hc
end LogicLineages.PersistentMarking.PortTermStateProof
