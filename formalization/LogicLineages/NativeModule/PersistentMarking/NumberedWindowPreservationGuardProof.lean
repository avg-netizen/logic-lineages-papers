module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowNumberedDomainProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowApplicationDomainProof (annotation)
open NumberedWindowNumberedDomainProof (ArgsGuard)
open TypeSupport (subtypes)

abbrev TermGuard (S : Spine.Signature) (K : List Ty) (q : NTerm) : Prop :=
  (∀ ρ, ρ ∈ support q → ρ ∈ K) ∧ ∀ f, f ∈ heads q → HeadInWindow S K f

theorem nilGuard {S K} : ArgsGuard S K .nil :=
  ⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h)⟩

theorem consGuard {S K q qs} (hq : TermGuard S K q) (hqs : ArgsGuard S K qs) :
    ArgsGuard S K (.cons q qs) :=
  ⟨fun t ht => (List.mem_append.mp ht).elim (hq.1 t) (hqs.1 t),
    fun g hg => (List.mem_append.mp hg).elim (hq.2 g) (hqs.2 g)⟩

theorem consParts {S K q qs} (h : ArgsGuard S K (.cons q qs)) :
    TermGuard S K q ∧ ArgsGuard S K qs :=
  ⟨⟨fun t ht => h.1 t (List.mem_append_left _ ht),
      fun g hg => h.2 g (List.mem_append_left _ hg)⟩,
    ⟨fun t ht => h.1 t (List.mem_append_right _ ht),
      fun g hg => h.2 g (List.mem_append_right _ hg)⟩⟩

theorem ordinaryParts {S K C f bs} (h : InWindow S K C f.result (.ordinary f bs)) :
    BaseTyped C bs f.arguments ∧ HeadInWindow S K f ∧ ArgsGuard S K bs := by
  have hb : BaseTyped C bs f.arguments := by
    cases h.1 with
    | ordinary hb => exact hb
  exact ⟨hb,h.2.2 f List.mem_cons_self,
    ⟨fun t ht => h.2.1 t (List.mem_append_right _ ht),
      fun g hg => h.2.2 g (List.mem_cons_of_mem _ hg)⟩⟩

theorem ordinary {S K C f bs} (hb : BaseTyped C bs f.arguments)
    (hf : HeadInWindow S K f) (hg : ArgsGuard S K bs) :
    InWindow S K C f.result (.ordinary f bs) :=
  ⟨.ordinary hb,
    fun t ht => (List.mem_append.mp ht).elim (hf.2 t) (hg.1 t),
    fun g h => by
      change g ∈ f :: argsHeads bs at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hf
      · exact hg.2 g h⟩

theorem lamBody {S K C σ τ q} (h : InWindow S K C (.arrow σ τ) (.lam σ q)) :
    InWindow S K (C.push σ) τ q := by
  have ht : Typed (C.push σ) q τ := by
    cases h.1 with
    | lam hq => exact hq
  exact ⟨ht,fun t hp => h.2.1 t (List.mem_append_right _ hp),h.2.2⟩

theorem lam {S K C σ τ q}
    (hRoot : ∀ t, t ∈ subtypes (.arrow σ τ) → t ∈ K)
    (h : InWindow S K (C.push σ) τ q) : InWindow S K C (.arrow σ τ) (.lam σ q) := by
  refine ⟨.lam h.1,?_,h.2.2⟩
  intro t ht
  simp only [support,NTerm.type,annotation h.1,List.mem_append] at ht
  rcases ht with (hr | hs) | hq
  · exact hRoot t hr
  · exact hRoot t (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
  · exact h.2.1 t hq

theorem appParts {S K C σ τ q a} (h : InWindow S K C τ (.auxApp σ τ q a)) :
    InWindow S K C (.arrow σ τ) q ∧ InWindow S K C σ a := by
  have ht : Typed C q (.arrow σ τ) ∧ Typed C a σ := by
    cases h.1 with
    | auxApp hq ha => exact ⟨hq,ha⟩
  exact
    ⟨⟨ht.1,fun t hp => h.2.1 t (List.mem_append_left _ (List.mem_append_right _ hp)),
        fun f hf => h.2.2 f (List.mem_append_left _ hf)⟩,
      ⟨ht.2,fun t hp => h.2.1 t (List.mem_append_right _ hp),
        fun f hf => h.2.2 f (List.mem_append_right _ hf)⟩⟩

theorem ordinaryGuard {S K f bs} (hf : HeadInWindow S K f) (hg : ArgsGuard S K bs) :
    TermGuard S K (.ordinary f bs) :=
  ⟨fun t ht => (List.mem_append.mp ht).elim (hf.2 t) (hg.1 t),
    fun g h => by
      change g ∈ f :: argsHeads bs at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hf
      · exact hg.2 g h⟩

theorem numberedGuard {S K f τ k bs es} (hf : HeadInWindow S K f)
    (ht : ∀ ρ, ρ ∈ subtypes τ → ρ ∈ K) (hb : ArgsGuard S K bs) (he : ArgsGuard S K es) :
    TermGuard S K (.numbered f τ k bs es) := by
  refine ⟨?_,?_⟩
  · intro t h
    simp only [support,List.mem_append] at h
    rcases h with ((hd | hr) | hbs) | hes
    · exact hf.2 t hd
    · exact ht t hr
    · exact hb.1 t hbs
    · exact he.1 t hes
  · intro g h
    simp only [heads,List.mem_cons,List.mem_append] at h
    rcases h with rfl | hbs | hes
    · exact hf
    · exact hb.2 g hbs
    · exact he.2 g hes

theorem lamGuard {S K σ q} (hRoot : ∀ t, t ∈ subtypes (.arrow σ q.type) → t ∈ K)
    (h : TermGuard S K q) : TermGuard S K (.lam σ q) := by
  refine ⟨?_,h.2⟩
  intro t ht
  simp only [support,NTerm.type,List.mem_append] at ht
  rcases ht with (hr | hs) | hq
  · exact hRoot t hr
  · exact hRoot t (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
  · exact h.1 t hq

theorem appGuard {S K σ τ q a} (hk : DecisionSourceUniverse.Closed K)
    (hArrow : Ty.arrow σ τ ∈ K) (hq : TermGuard S K q) (ha : TermGuard S K a) :
    TermGuard S K (.auxApp σ τ q a) := by
  refine ⟨?_,?_⟩
  · intro ρ h
    simp only [support,List.mem_append] at h
    rcases h with ((hτ | hσ) | hq') | ha'
    · exact NumberedWindowApplicationDomainProof.arrowRight hk hArrow ρ hτ
    · exact NumberedWindowApplicationDomainProof.arrowLeft hk hArrow ρ hσ
    · exact hq.1 ρ hq'
    · exact ha.1 ρ ha'
  · intro f h
    exact (List.mem_append.mp h).elim (hq.2 f) (ha.2 f)

private theorem toExtrasFixed (C : Spine.BoundContext) (qs : NArgs) (types : List Ty)
    (h : BaseTyped C qs types) : ExtrasTyped C qs := by
  cases qs with
  | nil => exact .nil
  | cons q tail =>
    cases h with
    | cons hq htail => exact .cons hq (toExtrasFixed C tail _ htail)
termination_by sizeOf qs

theorem toExtras {C qs types} (h : BaseTyped C qs types) : ExtrasTyped C qs :=
  toExtrasFixed C qs types h

theorem annotated {S K C τ q} (h : InWindow S K C τ q) : InWindow S K C q.type q := by
  rw [annotation h.1]
  exact h

end LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof
