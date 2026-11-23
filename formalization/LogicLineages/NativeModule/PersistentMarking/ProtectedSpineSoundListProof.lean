module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundStageTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundBitProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOccurrenceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundListProof
open Spine DecisionPorts HereditaryDomainCode PortNormalization
open MarkedConstructorTests (terms)
open MarkedConstructorTargets (Delete SplitList Matches Replaces)
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets

theorem atMember {qs : Args} {q : Expr} (h : q ∈ terms qs) : ∃ i, At qs i q := by
  cases qs with
  | nil => cases h
  | cons a qs =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact ⟨0,.here⟩
    · obtain ⟨i,hi⟩ := atMember (qs := qs) ht
      exact ⟨i+1,.there hi⟩
termination_by sizeOf qs

theorem baseMember (F : Inputs S) (Γ : Context) {bs : Args} {xs : List MarkedExtras.Tagged}
    {a : MarkedExtras.Tagged} (hb : BaseRelated F Γ xs bs) (h : a ∈ xs) :
    ∃ i q, At bs i q ∧ a.1 = q.type ∧ Related F a.1 Γ a.2 (some q) := by
  induction hb with
  | nil => cases h
  | cons hq hqs ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact ⟨0,_,.here,rfl,hq⟩
    · obtain ⟨i,q,hi,he,hr⟩ := ih ht
      exact ⟨i+1,q,.there hi,he,hr⟩

theorem deleteTerms {t : Expr} {rest : List Expr} {ts : Args} (h : Delete t (terms ts) rest) :
    ∃ ts', Remove ts t ts' ∧ terms ts' = rest := by
  cases ts with
  | nil => cases h
  | cons a ts =>
    change Delete t (a::terms ts) rest at h
    cases h with
    | here => exact ⟨_,.here,rfl⟩
    | there ht =>
      obtain ⟨ts',hm,rfl⟩ := deleteTerms (ts := ts) ht
      exact ⟨.cons a ts',.there hm,rfl⟩
termination_by sizeOf ts

theorem splitTerms {ts : Args} {ys zs : List Expr} (h : SplitList (terms ts) ys zs) :
    ∃ left right, Split ts left right ∧ terms left = ys ∧ terms right = zs := by
  cases ts with
  | nil =>
    change SplitList [] ys zs at h
    cases h
    exact ⟨.nil,.nil,.nil,rfl,rfl⟩
  | cons a ts =>
    change SplitList (a::terms ts) ys zs at h
    cases h with
    | left ht =>
      obtain ⟨l,r,hs,rfl,rfl⟩ := splitTerms (ts := ts) ht
      exact ⟨.cons a l,r,.left hs,rfl,rfl⟩
    | right ht =>
      obtain ⟨l,r,hs,rfl,rfl⟩ := splitTerms (ts := ts) ht
      exact ⟨l,.cons a r,.right hs,rfl,rfl⟩
termination_by sizeOf ts

theorem splitBase (F : Inputs S) (Γ : Context) {bs : Args} {xs ys zs : List MarkedExtras.Tagged}
    (hb : BaseRelated F Γ xs bs) (h : SplitList xs ys zs) :
    ∃ left right, Split bs left right ∧ BaseRelated F Γ ys left ∧ BaseRelated F Γ zs right := by
  induction hb generalizing ys zs with
  | nil => cases h; exact ⟨.nil,.nil,.nil,.nil,.nil⟩
  | cons hq hqs ih =>
    cases h with
      | left ht =>
        obtain ⟨l,r,hs,hl,hr⟩ := ih ht
        exact ⟨_,_,.left hs,.cons hq hl,hr⟩
      | right ht =>
        obtain ⟨l,r,hs,hl,hr⟩ := ih ht
        exact ⟨_,_,.right hs,hl,.cons hq hr⟩

theorem deleteMem {t : Expr} {xs ys : List Expr} (h : Delete t xs ys) :
    t ∈ xs ∧ (∀ u, u ∈ ys → u ∈ xs) := by
  induction h with
  | here => exact ⟨List.mem_cons_self,fun _ => List.mem_cons_of_mem _⟩
  | there _ ih =>
    exact ⟨List.mem_cons_of_mem _ ih.1,fun u h => (List.mem_cons.mp h).elim
      (fun h => List.mem_cons.mpr (Or.inl h)) (fun h => List.mem_cons_of_mem _ (ih.2 u h))⟩

theorem splitMem {xs ys zs : List Expr} (h : SplitList xs ys zs) (t : Expr) :
    (t ∈ ys → t ∈ xs) ∧ (t ∈ zs → t ∈ xs) := by
  induction h with
  | nil => simp
  | left _ ih =>
    exact ⟨fun h => (List.mem_cons.mp h).elim
      (fun h => List.mem_cons.mpr (Or.inl h)) (fun h => List.mem_cons_of_mem _ (ih.1 h)),
      fun h => List.mem_cons_of_mem _ (ih.2 h)⟩
  | right _ ih =>
    exact ⟨fun h => List.mem_cons_of_mem _ (ih.1 h),fun h => (List.mem_cons.mp h).elim
      (fun h => List.mem_cons.mpr (Or.inl h)) (fun h => List.mem_cons_of_mem _ (ih.2 h))⟩

theorem matching (F : Inputs S) (Γ : Context) (hw : WellFormed F.data.types F.data.ports Γ)
    {bs : Args} {xs : List MarkedExtras.Tagged} (hb : BaseRelated F Γ xs bs) :
    ∀ ts, (∀ t, t ∈ terms ts → Observed F Γ t) →
      Matches (domain F) Γ xs (terms ts) → Matching S bs ts := by
  induction hb with
  | nil =>
    intro ts _ h
    cases ts with
    | nil => exact .nil
    | cons t ts => cases h
  | cons hq hqs ih =>
    intro ts hObs h
    generalize ht : terms ts = tsList at h
    cases h with
    | cons hd hb hm =>
      rw [←ht] at hd
      obtain ⟨rest,hr,he⟩ := deleteTerms hd
      rw [←he] at hm
      exact .cons hr (ProtectedSpineSoundBitProof.tagged F Γ _ _ _ hw
        (hObs _ (deleteMem hd).1) hq false hb)
        (ih rest (fun u hu => hObs u ((deleteMem hd).2 u (he ▸ hu))) hm)

theorem coverage (F : Inputs S) (Γ : Context) (hw : WellFormed F.data.types F.data.ports Γ)
    {owners : Args} {xs : List MarkedExtras.Tagged} (hb : BaseRelated F Γ xs owners)
    (ts : Args) (ho : ∀ t, t ∈ terms ts → Observed F Γ t)
    (h : ∀ t, t ∈ terms ts → ∃ a, a ∈ xs ∧ MarkedConstructorTests.bit true (domain F) Γ a t = true) :
    Coverage S owners ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
    have ht : t ∈ terms (.cons t ts) := List.mem_cons_self
    obtain ⟨a,hm,ha⟩ := h t ht
    obtain ⟨i,q,hi,_,hr⟩ := baseMember F Γ hb hm
    exact .cons hi (ProtectedSpineSoundBitProof.tagged F Γ q t a hw (ho t ht) hr true ha)
      (coverage F Γ hw hb ts (fun u hu => ho u (List.mem_cons_of_mem _ hu)) (fun u hu => h u (List.mem_cons_of_mem _ hu)))
termination_by sizeOf ts

theorem multiset (F : Inputs S) (Γ : Context) (hw : WellFormed F.data.types F.data.ports Γ)
    {bs ts : Args} {xs : List MarkedExtras.Tagged} (hb : BaseRelated F Γ xs bs)
    (ho : ∀ t, t ∈ terms ts → Observed F Γ t)
    (h : Replaces (domain F) Γ xs (terms ts)) : Multiset S bs ts := by
  obtain ⟨kept,removed,matched,added,hs,ht,hn,hm,hc⟩ := h
  obtain ⟨l,r,hbs,hl,hr⟩ := splitBase F Γ hb hs
  obtain ⟨m,a,hts,rfl,rfl⟩ := splitTerms ht
  have hNonempty : Spine.Nonempty r := by
    cases hr with
    | nil => exact False.elim (hn rfl)
    | cons => trivial
  exact .replace hbs hts hNonempty (matching F Γ hw hl m (fun t h => ho t ((splitMem ht t).1 h)) hm)
    (coverage F Γ hw hr a (fun t h => ho t ((splitMem ht t).2 h)) hc)

end LogicLineages.PersistentMarking.ProtectedSpineSoundListProof
