module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureTargets
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport

private theorem rootAllowed {Symbol : Type} {arity : Symbol → Nat}
    {K : Ty → Prop} {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ)
    (h : typesAllowed K q) : K τ := by
  cases q <;> first | exact h | exact h.1

private theorem arrowDomain {K : Ty → Prop} (hc : SubtypeClosed K)
    {σ τ : Ty} (h : K (.arrow σ τ)) : K σ := by
  apply hc _ h
  simp [Ty.subtypes, Ty.mem_subtypes_self]

private theorem arrowCodomain {K : Ty → Prop} (hc : SubtypeClosed K)
    {σ τ : Ty} (h : K (.arrow σ τ)) : K τ := by
  apply hc _ h
  simp [Ty.subtypes, Ty.mem_subtypes_self]

private theorem suffixResult {K : Ty → Prop} (hc : SubtypeClosed K)
    (types : List Ty) (τ : Ty) (h : K (arrows types τ)) : K τ := by
  induction types with
  | nil => exact h
  | cons σ rest ih => exact ih (arrowCodomain hc h)

theorem renameAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ {Δ : List Ty} (ρ : Renaming Γ Δ),
      typesAllowed K q → typesAllowed K (renameTerm q ρ) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ {Δ : List Ty} (ρ : Renaming Γ Δ),
      argumentTypesAllowed K args → argumentTypesAllowed K (renameArguments args ρ)) with
  | var v => intro Δ ρ h; exact h
  | lam body ih => intro Δ ρ h; exact ⟨h.1, h.2.1, ih ρ.lift h.2.2⟩
  | ordinary hd base ih => intro Δ ρ h; exact ⟨h.1, ih ρ h.2⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ ρ h
      exact ⟨h.1, ihb ρ h.2.1, ihe ρ h.2.2⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i Δ ρ h
      exact ⟨ihq ρ h.1, ihr ρ h.2⟩

theorem renamingTypeClosure : TypeClosureTargets.RenamingTypeClosure := by
  intro Symbol arity K Γ Δ τ q ρ h
  exact renameAllowed K q ρ h

theorem markingTypeClosure : TypeClosureTargets.MarkingTypeClosure := by
  intro Symbol arity K Γ τ q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r h he; cases he
  | lam body ih =>
      intro r h he
      simp only [markSpine] at he
      cases hm : markSpine body with
      | none => simp [hm] at he
      | some out =>
          simp only [hm, Option.map_some, Option.some.injEq] at he
          subst r
          exact ⟨h.1, h.2.1, ih out h.2.2 hm⟩
  | ordinary hd base ih =>
      intro r h he
      cases he
      exact ⟨h.1, h.2, True.intro⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro r h he
      cases he
      exact h
  | nil => trivial
  | cons q rest ihq ihr => trivial

private theorem liftAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ Δ : List Ty} {τ : Ty}
    (env : MarkedSubstitution Symbol arity Γ Δ) (h : substitutionTypesAllowed K env) :
    substitutionTypesAllowed K (@liftSubstitution Symbol arity Γ Δ τ env) := by
  intro σ v hs
  cases v with
  | here => exact hs
  | there v => exact renameAllowed K (env v) (Renaming.weaken Δ τ) (h v hs)

theorem substituteAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ {Δ : List Ty} (env : MarkedSubstitution Symbol arity Γ Δ),
      typesAllowed K q → substitutionTypesAllowed K env →
      typesAllowed K (substituteTerm q env) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ {Δ : List Ty}
      (env : MarkedSubstitution Symbol arity Γ Δ),
      argumentTypesAllowed K args → substitutionTypesAllowed K env →
      argumentTypesAllowed K (substituteArguments args env)) with
  | var v => intro Δ env h he; exact he v h
  | lam body ih =>
      intro Δ env h he
      exact ⟨h.1, h.2.1, ih (liftSubstitution env) h.2.2 (liftAllowed K env he)⟩
  | ordinary hd base ih => intro Δ env h he; exact ⟨h.1, ih env h.2 he⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ env h he
      exact ⟨h.1, ihb env h.2.1 he, ihe env h.2.2 he⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i Δ env h he
      exact ⟨ihq env h.1 he, ihr env h.2 he⟩

theorem substitutionTypeClosure : TypeClosureTargets.SubstitutionTypeClosure := by
  intro Symbol arity K Γ Δ τ q env h he
  exact substituteAllowed K q env h he

private theorem transportAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ : List Ty} {σ τ : Ty} (h : σ = τ)
    (q : MarkedTerm Symbol arity Γ σ) (hq : typesAllowed K q) :
    typesAllowed K (transportTerm h q) := by
  cases h
  exact hq

private theorem appendAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ xs : List Ty} (a : Arguments Symbol arity Γ xs) :
    ∀ {ys : List Ty} (b : Arguments Symbol arity Γ ys),
      argumentTypesAllowed K a → argumentTypesAllowed K b →
      argumentTypesAllowed K (appendArguments a b) := by
  induction a using Arguments.rec (motive_1 := fun _ _ _ => True) with
  | var v => trivial
  | lam body ih => trivial
  | ordinary hd base ih => trivial
  | marked hd output base extraTypes extras ihb ihe => trivial
  | nil => intro ys b ha hb; exact hb
  | cons q rest ihq ihr => intro ys b ha hb; exact ⟨ha.1, ihr b ha.2 hb⟩

private theorem emptyAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ Δ : List Ty} {σ τ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) (env : MarkedSubstitution Symbol arity Γ Δ)
    (h : σ = τ) (r : MarkedTerm Symbol arity Δ τ)
    (hq : typesAllowed K q) (he : substitutionTypesAllowed K env)
    (hr : applyOriginalWith q env (.nil : Arguments Symbol arity Δ []) h = some r) :
    typesAllowed K r := by
  have hn : applyOriginalWith q env (.nil : Arguments Symbol arity Δ []) h =
      some (transportTerm h (substituteTerm q env)) := by
    cases q <;> rfl
  rw [hn] at hr
  have hh := Option.some.inj hr
  rw [← hh]
  exact transportAllowed K h _ (substituteAllowed K q env hq he)

theorem applicationAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) (hc : SubtypeClosed K) {Γ : List Ty} {σ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) :
    ∀ {Δ types : List Ty} {τ : Ty} (env : MarkedSubstitution Symbol arity Γ Δ)
      (args : Arguments Symbol arity Δ types) (h : σ = arrows types τ)
      (r : MarkedTerm Symbol arity Δ τ),
      typesAllowed K q → substitutionTypesAllowed K env → argumentTypesAllowed K args →
      applyOriginalWith q env args h = some r → typesAllowed K r := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed K (.var v) env h r hq he hr
      | cons a rest => simp [applyOriginalWith] at hr
  | lam body ih =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed K (.lam body) env h r hq he hr
      | cons a rest =>
          have hc' := Ty.arrow.inj h
          have ha' := transportAllowed K hc'.1.symm a ha.1
          have hh : substitutionTypesAllowed K (extendEnvironment env (transportTerm hc'.1.symm a)) := by
            intro υ v hv
            cases v with
            | here => exact ha'
            | there v => exact he v hv
          exact ih (extendEnvironment env (transportTerm hc'.1.symm a)) rest hc'.2 r hq.2.2 hh ha.2 hr
  | ordinary hd base ih =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed K (.ordinary hd base) env h r hq he hr
      | cons a rest =>
          have hs := substituteAllowed K (.ordinary hd base) env hq he
          have ht : K τ := suffixResult hc _ τ (h ▸ hq.1)
          simp only [applyOriginalWith] at hr
          have hh := Option.some.inj hr
          rw [← hh]
          exact ⟨ht, hs.2, ha⟩
  | marked hd output base extraTypes extras ihb ihe =>
      intro Δ types τ env args h r hq he ha hr
      cases args with
      | nil => exact emptyAllowed K (.marked hd output base extraTypes extras) env h r hq he hr
      | cons a rest =>
          have hs := substituteAllowed K (.marked hd output base extraTypes extras) env hq he
          have ht : K τ := suffixResult hc _ τ (h ▸ hq.1)
          simp only [applyOriginalWith] at hr
          have hh := Option.some.inj hr
          rw [← hh]
          exact ⟨ht, hs.2.1, appendAllowed K _ _ hs.2.2 ha⟩
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem simultaneousApplicationTypeClosure : TypeClosureTargets.SimultaneousApplicationTypeClosure := by
  intro Symbol arity K Γ Δ σ τ types q env args h r hc hq he ha hr
  exact applicationAllowed K hc q env args h r hq he ha hr

theorem retypingTypeClosure : TypeClosureTargets.RetypingTypeClosure := by
  intro Symbol arity K Γ hd σ τ base types extras h ht
  exact ⟨ht, h.2⟩

private theorem groundArgumentsAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ : List Ty} (n : Nat)
    (f : Fin n → MarkedTerm Symbol arity Γ .ground) :
    argumentTypesAllowed K (groundArguments n f) ↔ ∀ i, typesAllowed K (f i) := by
  induction n with
  | zero => simp [groundArguments, argumentTypesAllowed]
  | succ n ih =>
      simp only [groundArguments, argumentTypesAllowed, ih]
      exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

private theorem allSubtypes {K : Ty → Prop} (hc : SubtypeClosed K) (τ : Ty) :
    (∀ σ ∈ τ.subtypes.toFinset, K σ) ↔ K τ := by
  constructor
  · intro h
    exact h τ (List.mem_toFinset.mpr (Ty.mem_subtypes_self τ))
  · intro h σ hs
    exact hc τ h σ (List.mem_toFinset.mp hs)

theorem literalEmbeddingTypeClosure : TypeClosureTargets.LiteralEmbeddingTypeClosure := by
  intro Symbol arity K Γ τ q hc
  induction q with
  | var v =>
      simpa only [embed, typesAllowed, typeSupport, Finset.union_empty] using (allSubtypes hc _).symm
  | app f a ihf iha =>
      simp only [embed, typesAllowed, argumentTypesAllowed, typeSupport, Finset.mem_union]
      simp only [or_imp, forall_and, allSubtypes hc, and_true]
      rw [← ihf, ← iha]
  | lam body ih =>
      simp only [embed, typesAllowed, typeSupport, Finset.mem_union, or_imp, forall_and,
        allSubtypes hc, ← ih]
      constructor
      · intro h; exact ⟨h.1, h.2.2⟩
      · intro h; exact ⟨h.1, arrowDomain hc h.1, h.2⟩
  | zeroC =>
      simpa only [embed, typesAllowed, argumentTypesAllowed, typeSupport, Finset.union_empty, and_true] using (allSubtypes hc _).symm
  | succC =>
      simpa only [embed, typesAllowed, argumentTypesAllowed, typeSupport, Finset.union_empty, and_true] using (allSubtypes hc _).symm
  | caseC τ =>
      simpa only [embed, typesAllowed, argumentTypesAllowed, typeSupport, Finset.union_empty, and_true] using (allSubtypes hc _).symm
  | recC τ =>
      simpa only [embed, typesAllowed, argumentTypesAllowed, typeSupport, Finset.union_empty, and_true] using (allSubtypes hc _).symm
  | ranked s args ih =>
      simp only [embed, typesAllowed, typeSupport, Finset.mem_union,
        or_imp, forall_and, allSubtypes hc, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        intro σ hs
        obtain ⟨i, hi⟩ := hs
        exact (ih i).mp ((groundArgumentsAllowed K (arity s) (fun i => embed (args i))).mp h.2 i) σ hi
      · intro h
        refine ⟨h.1, ?_⟩
        apply (groundArgumentsAllowed K (arity s) (fun i => embed (args i))).mpr
        intro i
        apply (ih i).mpr
        intro σ hs
        exact h.2 σ ⟨i, hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureProof
