module
public import LogicLineages.OrdinalComparison.SourceNamedPortsTargets
public import LogicLineages.OrdinalComparison.SourceNamedWeakeningProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedPortsProof
open SourceNamedSyntax SourceNamedWeakening SourceNamedWeakeningProof SourcePortContexts SourceNamedPorts SourceNamedPortsTargets

theorem spelledPortInjective : SpelledPortInjective := by
  intro Γ B i j h
  apply Fin.ext
  exact Nat.add_left_cancel h

theorem spelledPortFresh : SpelledPortFresh := by
  intro Γ B i p hp
  have h := (concreteFreshName Γ).2 p hp
  unfold spellPort
  omega

theorem realizedPortTypes : RealizedPortTypes := by
  intro Γ B P
  simp [realizedContext, contextTypes, portTypes, List.map_append, List.map_map, Function.comp_def]

private theorem lookup_member {Γ : Context} {x : Nat} {σ : Ty}
    (h : lookup Γ x = some σ) : (x, σ) ∈ Γ := by
  induction Γ with
  | nil => cases h
  | cons p Γ ih =>
    rcases p with ⟨y, τ⟩
    by_cases e : x = y
    · subst x
      have ht : τ = σ := by simpa [lookup] using h
      subst τ
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, e] using h))

private theorem lookup_none_of_fresh (Γ : Context) (x : Nat)
    (h : ∀ p ∈ Γ, x ≠ p.1) : lookup Γ x = none := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    have hp := h p (by simp)
    simp only [lookup, if_neg hp]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

private theorem base_lookup (Γ : Context) {B : Nat} (P : PortContext B)
    (x : Nat) (σ : Ty) (h : lookup Γ x = some σ) :
    lookup (realizedContext Γ P) x = some σ := by
  induction P with
  | nil => exact h
  | cons p P ih =>
    have hn : x ≠ spellPort Γ p.1 := fun e => spelledPortFresh Γ B p.1 (x, σ) (lookup_member h) e.symm
    simpa only [realizedContext, List.map_cons, List.cons_append, lookup, if_neg hn] using ih

private theorem port_lookup (Γ : Context) {B : Nat} (P : PortContext B)
    (hn : (P.map Prod.fst).Nodup) (i : Fin B) (σ : Ty) (hm : (i, σ) ∈ P) :
    lookup (realizedContext Γ P) (spellPort Γ i) = some σ := by
  induction P with
  | nil => cases hm
  | cons p P ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [realizedContext, lookup]
    · have hne : i ≠ p.1 := by
        intro he
        have hmem : p.1 ∈ P.map Prod.fst := List.mem_map.mpr ⟨(i, σ), hm, he⟩
        exact (List.nodup_cons.mp hn).1 hmem
      have hnames : spellPort Γ i ≠ spellPort Γ p.1 := fun he => hne (spelledPortInjective Γ B he)
      simpa only [realizedContext, List.map_cons, List.cons_append, lookup, if_neg hnames]
        using ih (List.nodup_cons.mp hn).2 hm

theorem realizedPortLookup : RealizedPortLookup := by
  intro Γ B P hn
  exact ⟨base_lookup Γ P, port_lookup Γ P hn⟩

theorem realizedFreshExtension : RealizedFreshExtension := by
  intro Γ B P i σ hi
  constructor
  · apply lookup_none_of_fresh
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      intro he
      have heid : i = q.1 := spelledPortInjective Γ B he
      exact hi (List.mem_map.mpr ⟨q, hq, heid.symm⟩)
    · exact spelledPortFresh Γ B i p hp
  · rfl

private theorem arbitrary_weakening_resolution {Γ : Context} (x : Nat) (σ : Ty)
    (hx : lookup Γ x = none) : ResolutionAlong (weakenInclusion x σ hx)
      (Renaming.weaken (contextTypes Γ) σ) := by
  intro y τ hy
  have hn : y ≠ x := by intro e; subst y; rw [hx] at hy; cases hy
  simp only [resolve, dif_neg hn]
  rfl

theorem actualNamedPortWeakening : ActualNamedPortWeakening := by
  intro Symbol arity Γ B P i σ hi
  let hx := (realizedFreshExtension Γ B P i σ hi).1
  refine ⟨hx, ?_⟩
  intro τ t
  exact ⟨namedRenamingErasure Symbol arity _ _ τ t _ _
    (arbitrary_weakening_resolution (spellPort Γ i) σ hx),
    namedRenamingFootprint Symbol arity _ _ τ t _⟩

end LogicLineages.OrdinalComparison.Source.SourceNamedPortsProof
