module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceTargets
public import LogicLineages.NativeModule.PersistentMarking.DecisionInventoryProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionPortsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceBasicProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse

def ArgsFacts (K : List Ty) (V : List Name) (H : List Head) (Γ : Context) (qs : Args) : Prop :=
  (∀ σ, σ ∈ auxiliaryArgs qs → σ ∈ K) ∧
  (∀ f, f ∈ headsArgs qs → f ∈ H) ∧
  (∀ n, freeOccursArgs n qs = true → AllowedName V Γ n)

theorem argsFacts (K : List Ty) (V : List Name) (H : List Head) (Γ : Context) (qs : Args) :
    ArgsUniverse K V H Γ qs ↔ ArgsFacts K V H Γ qs := by
  cases qs with
  | nil =>
    constructor
    · intro _; exact ⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h),fun _ h => Bool.noConfusion h⟩
    · intro _; trivial
  | cons q qs =>
    have ih := argsFacts K V H Γ qs
    constructor
    · rintro ⟨hq,hqs⟩; have hr := ih.mp hqs
      refine ⟨?_,?_,?_⟩
      · intro σ h; exact (List.mem_append.mp h).elim (hq.1 σ) (hr.1 σ)
      · intro f h; exact (List.mem_append.mp h).elim (hq.2.1 f) (hr.2.1 f)
      · intro n h; have hh : freeOccurs n q = true ∨ freeOccursArgs n qs = true := by simpa only [freeOccursArgs,Bool.or_eq_true] using h
        exact hh.elim (hq.2.2 n) (hr.2.2 n)
    · intro h
      refine ⟨⟨?_,?_,?_⟩,ih.mpr ⟨?_,?_,?_⟩⟩
      · intro σ hσ; exact h.1 σ (List.mem_append_left _ hσ)
      · intro f hf; exact h.2.1 f (List.mem_append_left _ hf)
      · intro n hn; exact h.2.2 n (by simp only [freeOccursArgs,hn,Bool.true_or])
      · intro σ hσ; exact h.1 σ (List.mem_append_right _ hσ)
      · intro f hf; exact h.2.1 f (List.mem_append_right _ hf)
      · intro n hn; exact h.2.2 n (by simp only [freeOccursArgs,hn,Bool.or_true])

termination_by sizeOf qs

theorem lamChild (K V H Γ σ q) (h : Universe K V H Γ (.lam σ q)) : Universe K V H Γ q :=
  ⟨fun τ hτ => h.1 τ (List.mem_append_right _ hτ),h.2.1,h.2.2⟩

theorem headBase (K V H Γ f bs) (h : Universe K V H Γ (.head f bs)) : ArgsUniverse K V H Γ bs :=
  (argsFacts K V H Γ bs).mpr ⟨fun τ hτ => h.1 τ (List.mem_append_right _ hτ),
    fun g hg => h.2.1 g (List.mem_cons_of_mem _ hg),h.2.2⟩

theorem markedBase (K V H Γ f τ bs es) (h : Universe K V H Γ (.marked f τ bs es)) : ArgsUniverse K V H Γ bs :=
  (argsFacts K V H Γ bs).mpr ⟨fun υ hυ => h.1 υ (List.mem_append_left _ (List.mem_append_right _ hυ)),
    fun g hg => h.2.1 g (List.mem_cons_of_mem _ (List.mem_append_left _ hg)),
    fun n hn => h.2.2 n (by simp only [freeOccurs,hn,Bool.true_or])⟩

theorem markedExtras (K V H Γ f τ bs es) (h : Universe K V H Γ (.marked f τ bs es)) : ArgsUniverse K V H Γ es :=
  (argsFacts K V H Γ es).mpr ⟨fun υ hυ => h.1 υ (List.mem_append_right _ hυ),
    fun g hg => h.2.1 g (List.mem_cons_of_mem _ (List.mem_append_right _ hg)),
    fun n hn => h.2.2 n (by simp only [freeOccurs,hn,Bool.or_true])⟩

theorem subtypeSelf (τ : Ty) : τ ∈ subtypes τ := by cases τ <;> simp [subtypes]
theorem rootType : DecisionSourceTargets.RootType := by
  intro K V H Γ q h
  exact h.1 q.type (DecisionInventoryProof.containsLiteral q q.type
    (TypeSupportFoundationProof.rootSupport q q.type (subtypeSelf q.type)))

theorem initial : DecisionSourceTargets.InitialUniverse := by
  intro s t σ τ hs ht hos hot
  refine ⟨?_,?_,?_,?_⟩
  · intro α hα β hβ
    rcases List.mem_append.mp hα with hα|hα
    · have ha := (DecisionInventoryProof.ordinaryExact EmptyContext s σ hs hos α).mpr hα
      have hb := DecisionInventoryProof.auxiliaryClosed s α ha β hβ
      exact List.mem_append_left _ ((DecisionInventoryProof.ordinaryExact EmptyContext s σ hs hos β).mp hb)
    · have ha := (DecisionInventoryProof.ordinaryExact EmptyContext t τ ht hot α).mpr hα
      have hb := DecisionInventoryProof.auxiliaryClosed t α ha β hβ
      exact List.mem_append_right _ ((DecisionInventoryProof.ordinaryExact EmptyContext t τ ht hot β).mp hb)
  · intro α hα; exact List.mem_append_left _ ((DecisionInventoryProof.ordinaryExact EmptyContext s σ hs hos α).mp hα)
  · intro f hf; exact hf
  · intro n hn; exact Or.inl (List.mem_append_left _ ((DecisionInventoryProof.freeExact s n).mpr hn))

theorem sourceAt : DecisionSourceTargets.SourceAt := by
  intro K V H Γ qs i q hu ha
  induction ha with
  | here => exact hu.1
  | there h ih => exact ih hu.2

theorem occurrence : DecisionSourceTargets.SourceOccurrence := by
  intro K V H Γ stack q locals r hu h
  have go : Universe K V H Γ q → Universe K V H Γ r := by
    clear hu
    induction h using Occurs.rec
      (motive_2 := fun _ qs _ r _ => ArgsUniverse K V H Γ qs → Universe K V H Γ r) with
    | root => exact id
    | lam h ih => intro hu; exact ih (lamChild _ _ _ _ _ _ hu)
    | head h ih => intro hu; exact ih (headBase _ _ _ _ _ _ hu)
    | markedBase h ih => intro hu; exact ih (markedBase _ _ _ _ _ _ _ _ hu)
    | markedExtra h ih => intro hu; exact ih (markedExtras _ _ _ _ _ _ _ _ hu)
    | here h ih => rename_i hu; exact ih hu.1
    | there h ih => rename_i hu; exact ih hu.2
  exact go hu

theorem weakening : DecisionSourceTargets.UniverseWeakening := by
  intro K V H Γ Δ q he hu
  refine ⟨hu.1,hu.2.1,?_⟩
  intro n hn
  rcases hu.2.2 n hn with hv|hp
  · exact Or.inl hv
  · obtain ⟨i,hi,hq⟩ := hp
    exact Or.inr ⟨i,he.2 i _ hi,hq⟩
end LogicLineages.PersistentMarking.DecisionSourceBasicProof
