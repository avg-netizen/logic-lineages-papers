import LogicLineages.PersistentMarking.NumberedWindowFrameTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFrameInclusionProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowClosing NumberedWindowPreservationTargets NumberedWindowFrameTargets

private theorem head {S K L f} (h : WindowInclusion K L)
    (hf : HeadInWindow S K f) : HeadInWindow S L f :=
  ⟨hf.1,fun t ht => h t (hf.2 t ht)⟩

theorem admitted {S K L C τ q} (h : WindowInclusion K L)
    (hq : InWindow S K C τ q) : InWindow S L C τ q :=
  ⟨hq.1,fun t ht => h t (hq.2.1 t ht),fun f hf => head h (hq.2.2 f hf)⟩

theorem raw {S K L q r} (h : WindowInclusion K L) (hs : RawStep S K q r) :
    RawStep S L q r := by
  induction hs using RawStep.rec (motive_2 := fun qs rs _ => RawArgsStep S L qs rs) with
  | mark => exact .mark
  | lower => exact .lower
  | select hg ht ha => exact .select hg ht ha
  | copy hp hg => exact .copy hp (head h hg)
  | stat he hg hr => exact .stat he (head h hg) hr
  | fabs => exact .fabs
  | beta => exact .beta
  | bottom hn => exact .bottom hn
  | lam _ ih => exact .lam ih
  | ordinaryBase _ ih => exact .ordinaryBase ih
  | numberedBase _ ih => exact .numberedBase ih
  | numberedExtra _ ih => exact .numberedExtra ih
  | auxFunction _ ih => exact .auxFunction ih
  | first _ ih => exact .first ih
  | later _ ih => exact .later ih

theorem primary {S K L C τ q r} (h : WindowInclusion K L) (he : Primary S K C τ q r) :
    Primary S L C τ q r := by
  induction he using Primary.rec (motive_2 := fun C ts qs rs _ => OrderedPrimary S L C ts qs rs) with
  | refl ht => exact .refl ht
  | symm _ ih => exact .symm ih
  | trans _ _ ihq ihr => exact .trans ihq ihr
  | ordinary hf hg he ht hb hc hp => exact .ordinary (head h hf) (head h hg) he ht hb hc hp
  | numbered hf hg he hb hc hs hp => exact .numbered (head h hf) (head h hg) he hb hc hs hp
  | lam _ ih => exact .lam ih
  | appFunction _ ha ih => exact .appFunction ih ha
  | appArgument hq _ ih => exact .appArgument hq ih
  | ordinaryArguments _ ih => exact .ordinaryArguments ih
  | numberedBase _ he ih => exact .numberedBase ih he
  | numberedExtras hb _ ih => exact .numberedExtras hb ih
  | nil => exact .nil
  | cons _ _ ihq ihs => exact .cons ihq ihs

theorem trace {S K L C τ q r} (h : WindowInclusion K L)
    (tr : TypedTrace S K C τ q r) :
    ∃ out : TypedTrace S L C τ q r,
      vertices out = vertices tr ∧ rawLength out = rawLength tr := by
  induction tr with
  | done ht => exact ⟨.done ht,rfl,rfl⟩
  | raw hq hr hs _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw hq hr (raw h hs) out,by simp only [vertices,hv],by simp only [rawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (primary h he) out,by simp only [vertices,hv],hl⟩

end LogicLineages.PersistentMarking.NumberedWindowFrameInclusionProof
