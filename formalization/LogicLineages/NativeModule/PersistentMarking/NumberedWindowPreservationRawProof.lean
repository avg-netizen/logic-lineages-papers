module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationHeadProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationReplacementProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationSubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationRawProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowPreservationGuardProof
open NumberedWindowApplicationDomainProof (annotation rootInWindow)
open NumberedWindowNumberedDomainProof (ArgsGuard)

def TermClaim (S : Spine.Signature) (K : List Ty) (q r : NTerm) : Prop :=
  ∀ C, InWindow S K C q.type q → r.type = q.type ∧ TermGuard S K r

private def ArgsClaim (S : Spine.Signature) (K : List Ty) (qs rs : NArgs) : Prop :=
  ∀ C, ExtrasTyped C qs → ArgsGuard S K qs → ArgsGuard S K rs

/-- A raw skeleton at an admitted source preserves the annotation and
footprint. This is not an assertion of lexical typing for unchecked skeleton
successors. The exact externally typed conclusion is supplied separately. -/
theorem rawGuard {S K q r} (hk : DecisionSourceUniverse.Closed K)
    (h : RawStep S K q r) : TermClaim S K q r := by
  induction h using RawStep.rec (motive_2 := fun qs rs _ => ArgsClaim S K qs rs) with
  | mark =>
    intro C h
    obtain ⟨_,hf,hb⟩ := ordinaryParts h
    exact ⟨rfl,numberedGuard hf (hk _ (rootInWindow h)) hb nilGuard⟩
  | lower =>
    intro C h
    exact ⟨rfl,h.2⟩
  | select hget harrow happ =>
    intro C h
    have hw := NumberedWindowPreservationHeadProof.select hk h hget harrow happ
    exact ⟨annotation hw.1,hw.2⟩
  | copy _ hg =>
    intro C h
    exact ⟨rfl,(NumberedWindowPreservationHeadProof.copy hk h hg).2⟩
  | stat _ hg hp =>
    intro C h
    obtain ⟨_,_,_,hb,_⟩ := NumberedWindowNumberedDomainProof.parts h
    exact ⟨rfl,ordinaryGuard hg (NumberedWindowPreservationReplacementProof.replacement hk hb hp)⟩
  | fabs =>
    intro C h
    exact ⟨rfl,(NumberedWindowNumberedDomainProof.openNumberedWindow S K C _ _ _ _ _ _ hk h).2⟩
  | beta =>
    intro C h
    have hw := NumberedWindowPreservationSubstitutionProof.beta hk h
    exact ⟨annotation hw.1,hw.2⟩
  | bottom _ =>
    intro C h
    exact ⟨rfl,hk _ (rootInWindow h),fun _ hp => False.elim (List.not_mem_nil hp)⟩
  | lam _ ih =>
    intro C h
    have hbody := lamBody h
    obtain ⟨he,hg⟩ := ih _ hbody
    refine ⟨by simp only [NTerm.type,he],lamGuard ?_ hg⟩
    rw [he]
    exact hk _ (rootInWindow h)
  | ordinaryBase _ ih =>
    intro C h
    obtain ⟨ht,hf,hb⟩ := ordinaryParts h
    exact ⟨rfl,ordinaryGuard hf (ih C (toExtras ht) hb)⟩
  | numberedBase _ ih =>
    intro C h
    obtain ⟨ht,_,hf,hb,he⟩ := NumberedWindowNumberedDomainProof.parts h
    exact ⟨rfl,numberedGuard hf (hk _ (rootInWindow h)) (ih C (toExtras ht) hb) he⟩
  | numberedExtra _ ih =>
    intro C h
    obtain ⟨_,ht,hf,hb,he⟩ := NumberedWindowNumberedDomainProof.parts h
    exact ⟨rfl,numberedGuard hf (hk _ (rootInWindow h)) hb (ih C ht he)⟩
  | auxFunction _ ih =>
    intro C h
    have parts := appParts h
    exact ⟨rfl,appGuard hk (rootInWindow parts.1) (ih C (annotated parts.1)).2 parts.2.2⟩
  | first _ ih =>
    intro C ht hg
    cases ht with
    | cons hq _ =>
      have parts := consParts hg
      exact consGuard (ih C (annotated ⟨hq,parts.1⟩)).2 parts.2
  | later _ ih =>
    intro C ht hg
    cases ht with
    | cons _ hrest =>
      have parts := consParts hg
      exact consGuard parts.1 (ih C hrest parts.2)

theorem raw {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C τ q) (hr : Typed C r τ) (hs : RawStep S K q r) :
    InWindow S K C τ r :=
  ⟨hr,(rawGuard hk hs C (annotated h)).2⟩

end LogicLineages.PersistentMarking.NumberedWindowPreservationRawProof
