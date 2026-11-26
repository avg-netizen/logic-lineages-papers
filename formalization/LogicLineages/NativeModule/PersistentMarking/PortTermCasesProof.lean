module

public import LogicLineages.NativeModule.PersistentMarking.PortTermStateProof
public import LogicLineages.NativeModule.PersistentMarking.PortHeadObservationProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedRenameSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.PortTermCasesProof
open Spine NameBridge PortNormalization RefinementRenamingTargets RefinementRenameSupport

theorem funCase (S : Signature) (F : Inputs S) (f g : Head) (ss ts : Args)
    (hs : PaperTerm S (.head f ss) f.result) (ht : PaperTerm S (.head g ts) g.result)
    (he : Equivalent S f g) (hty : f.result = g.result) (ih : MatchingMotive F ss ts) :
    WeakMotive F (.head f ss) (.head g ts) := by
  intro π Γ hp hw hu ho
  exact .funHead (paper S π _ _ hs) (paper S π _ _ ht) he hty
    (ih π Γ hp hw (DecisionSourceBasicProof.headBase _ _ _ _ _ _ hu)
      (PortHeadObservationProof.headObservations S F Γ _ _ hw ho))

theorem putCase (S : Signature) (F : Inputs S) (f : Head) (ss : Args) (t : Expr)
    (hs : PaperTerm S (.head f ss) f.result) (ht : PaperTerm S t f.result)
    (ih : WeakMotive F (.marked f f.result ss .nil) t) : WeakMotive F (.head f ss) t := by
  intro π Γ hp hw hu ho
  have hm : mark (rename π (.head f ss)) = some (rename π (.marked f f.result ss .nil)) := rfl
  exact .put (paper S π _ _ hs) (paper S π _ _ ht)
    (ih π Γ hp hw (DecisionSourceMarkProof.sourceMark _ _ _ _ _ _ hu hm) ho)

theorem selectCase (S : Signature) (F : Inputs S) (f : Head) (τ : Ty) (ss es : Args)
    (t q r : Expr) (i : Nat) (domains : List Ty)
    (hs : PaperTerm S (.marked f τ ss es) τ) (ht : PaperTerm S t τ)
    (ha : At ss i q ∨ At es i q) (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hc : apply q (ownerCopies f ss es domains) = some r) (ih : WeakMotive F r t) :
    WeakMotive F (.marked f τ ss es) t := by
  intro π Γ hp hw hu ho
  have hs' := paper S π _ _ hs
  have ha' := ha.elim (fun h => Or.inl (mapAt π h)) (fun h => Or.inr (mapAt π h))
  have hq' := ExtendedRenameSupport.typed π hq
  have hc' := ExtendedRenameSupport.call π hc
  rw [ExtendedRenameSupport.ownerCopies] at hc'
  exact .select hs' (paper S π _ _ ht) ha' hq' hc'
    (ih π Γ hp hw (PortTermStateProof.selected S F Γ _ _ _ _ _ _ _ _ hs' hu ha' hq' hc') ho)

theorem copyCase (S : Signature) (F : Inputs S) (f g : Head) (ss es ts : Args)
    (hs : PaperTerm S (.marked f g.result ss es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (hp : Precedes S f g) (ih : WholeMotive F f ss es ts) :
    WeakMotive F (.marked f g.result ss es) (.head g ts) := by
  intro π Γ hinj hw hu ho
  exact .copy (paper S π _ _ hs) (paper S π _ _ ht) hp
    (ih π Γ hinj hw (PortTermStateProof.owner S F Γ _ _ _ _ hu)
      (PortHeadObservationProof.headObservations S F Γ _ _ hw ho))

theorem statCase (S : Signature) (F : Inputs S) (f g : Head) (ss es ts : Args)
    (hs : PaperTerm S (.marked f g.result ss es) g.result) (ht : PaperTerm S (.head g ts) g.result)
    (he : Equivalent S f g) (ihm : MultisetMotive F ss ts) (ihw : WholeMotive F f ss es ts) :
    WeakMotive F (.marked f g.result ss es) (.head g ts) := by
  intro π Γ hp hw hu ho
  have hobs := PortHeadObservationProof.headObservations S F Γ _ _ hw ho
  exact .stat (paper S π _ _ hs) (paper S π _ _ ht) he
    (ihm π Γ hp hw (DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ hu) hobs)
    (ihw π Γ hp hw (PortTermStateProof.owner S F Γ _ _ _ _ hu) hobs)

theorem strictCase (S : Signature) (F : Inputs S) (q t r : Expr) (σ : Ty)
    (hs : PaperTerm S q σ) (ht : PaperTerm S t σ) (hm : mark q = some r)
    (ih : WeakMotive F r t) : StrictMotive F q t := by
  intro π Γ hp hw hu ho
  have hm' := ExtendedRenameSupport.mark π hm
  exact .intro (paper S π _ _ hs) (paper S π _ _ ht) hm'
    (ih π Γ hp hw (DecisionSourceMarkProof.sourceMark _ _ _ _ _ _ hu hm') ho)
end LogicLineages.PersistentMarking.PortTermCasesProof
