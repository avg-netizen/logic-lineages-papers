import LogicLineages.PersistentMarking.NumberedWindowPrimary
import LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryCases
import LogicLineages.PersistentMarking.NumberedWindowPreservationReplacementProof

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPreservationGuardProof NumberedWindowPreservationPrimaryCases
open NumberedWindowPreservationReplacementProof (permGuard)
open NumberedWindowNumberedDomainProof (ArgsGuard)

private def TermClaim (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (τ : Ty) (q r : NTerm) : Prop :=
  Typed C q τ ∧ Typed C r τ ∧ (TermGuard S K q ↔ TermGuard S K r)

private def ArgsClaim (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (types : List Ty) (qs rs : NArgs) : Prop :=
  BaseTyped C qs types ∧ BaseTyped C rs types ∧ (ArgsGuard S K qs ↔ ArgsGuard S K rs)

private theorem both {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (h : Primary S K C τ q r) : TermClaim S K C τ q r := by
  induction h using Primary.rec
    (motive_2 := fun C types qs rs _ => ArgsClaim S K C types qs rs) with
  | refl ht => exact ⟨ht,ht,Iff.rfl⟩
  | symm _ ih => exact ⟨ih.2.1,ih.1,ih.2.2.symm⟩
  | trans _ _ hq hr => exact ⟨hq.1,hr.2.1,hq.2.2.trans hr.2.2⟩
  | ordinary hf hg _ e hb hc hp =>
    exact ⟨.ordinary hb,e.symm ▸ Typed.ordinary hc,
      ⟨ordinaryExchange hb hg (permGuard hp),ordinaryExchange hc hf (permGuard hp.symm)⟩⟩
  | numbered hf hg _ hb hc he hp =>
    exact ⟨.numbered hb he,.numbered hc he,
      ⟨numberedExchange hk hb he hg (permGuard hp),numberedExchange hk hc he hf (permGuard hp.symm)⟩⟩
  | lam _ ih =>
    exact ⟨.lam ih.1,.lam ih.2.1,
      ⟨lamTransfer hk ih.1 ih.2.1 ih.2.2.mp,lamTransfer hk ih.2.1 ih.1 ih.2.2.mpr⟩⟩
  | appFunction _ ha ih =>
    exact ⟨.auxApp ih.1 ha,.auxApp ih.2.1 ha,
      ⟨appFunctionTransfer hk ih.1 ha ih.2.2.mp,appFunctionTransfer hk ih.2.1 ha ih.2.2.mpr⟩⟩
  | appArgument hq _ ih =>
    exact ⟨.auxApp hq ih.1,.auxApp hq ih.2.1,
      ⟨appArgumentTransfer hk hq ih.1 ih.2.2.mp,appArgumentTransfer hk hq ih.2.1 ih.2.2.mpr⟩⟩
  | ordinaryArguments _ ih =>
    exact ⟨.ordinary ih.1,.ordinary ih.2.1,
      ⟨ordinaryCong ih.1 ih.2.2.mp,ordinaryCong ih.2.1 ih.2.2.mpr⟩⟩
  | numberedBase _ he ih =>
    exact ⟨.numbered ih.1 he,.numbered ih.2.1 he,
      ⟨numberedBaseCong hk ih.1 he ih.2.2.mp,numberedBaseCong hk ih.2.1 he ih.2.2.mpr⟩⟩
  | numberedExtras hb _ ih =>
    have he := toExtras ih.1
    have hs := toExtras ih.2.1
    exact ⟨.numbered hb he,.numbered hb hs,
      ⟨numberedExtrasCong hk hb he ih.2.2.mp,numberedExtrasCong hk hb hs ih.2.2.mpr⟩⟩
  | nil => exact ⟨.nil,.nil,Iff.rfl⟩
  | cons _ _ hq ht =>
    exact ⟨.cons hq.1 ht.1,.cons hq.2.1 ht.2.1,
      ⟨fun h =>
        let p := consParts h
        consGuard (hq.2.2.mp p.1) (ht.2.2.mp p.2),
       fun h =>
        let p := consParts h
        consGuard (hq.2.2.mpr p.1) (ht.2.2.mpr p.2)⟩⟩

theorem primary {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (h : Primary S K C τ q r) : InWindow S K C τ q ↔ InWindow S K C τ r := by
  obtain ⟨hq,hr,hg⟩ := both hk h
  exact ⟨fun hw => ⟨hr,hg.mp hw.2⟩,fun hw => ⟨hq,hg.mpr hw.2⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryProof
