import LogicLineages.PersistentMarking.NumberedWindowNumberedDomainProof

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

end LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof
