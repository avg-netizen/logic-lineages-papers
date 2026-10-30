module
public import LogicLineages.OrdinalComparison.SourceNamedWeakeningTargets
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedWeakeningProof
open SourceNamedSyntax SourceNamedWeakening SourceNamedWeakeningTargets

private theorem name_bound (Γ : Context) : ∀ v ∈ Γ,
    v.1 ≤ (Γ.map Prod.fst).foldr max 0 := by
  induction Γ with
  | nil => simp
  | cons a Γ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.le_max_left _ _
    · exact (ih v hv).trans (Nat.le_max_right _ _)

private theorem lookup_mem {Γ : Context} {x : Nat} {σ : Ty}
    (h : lookup Γ x = some σ) : (x, σ) ∈ Γ := by
  induction Γ with
  | nil => cases h
  | cons a Γ ih =>
    rcases a with ⟨y, τ⟩
    by_cases e : x = y
    · subst x
      have ht : τ = σ := by simpa [lookup] using h
      subst σ
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, e] using h))

theorem concreteFreshName : ConcreteFreshName := by
  intro Γ
  have hb : ∀ v ∈ Γ, v.1 < freshName Γ := by
    intro v hv
    exact Nat.lt_succ_of_le (name_bound Γ v hv)
  refine ⟨?_, hb⟩
  cases h : lookup Γ (freshName Γ) with
  | none => rfl
  | some σ => exact False.elim (Nat.lt_irrefl _ (hb _ (lookup_mem h)))

theorem namedRenamingIdentity : NamedRenamingIdentity := by
  intro Symbol arity Γ τ t
  induction t with
  | var => rfl
  | app f a ihf iha => simp [namedRename, ihf, iha]
  | lam x body ih =>
    change NamedTerm.lam x (namedRename body _) = NamedTerm.lam x body
    exact congrArg (NamedTerm.lam x) ih
  | zeroC | succC | caseC | recC => rfl
  | ranked s args ih => simp [namedRename, ih]

private theorem lift_resolution {Γ Δ : Context} (inc : NameInclusion Γ Δ)
    (ρ : Renaming (contextTypes Γ) (contextTypes Δ)) (hr : ResolutionAlong inc ρ)
    (y : Nat) (τ : Ty) : ResolutionAlong (liftInclusion inc y τ) ρ.lift := by
  intro x σ h
  by_cases e : x = y
  · subst x
    have ht : τ = σ := by simpa [lookup] using h
    subst σ
    simp only [resolve]
    rfl
  · have hh : lookup Γ x = some σ := by simpa [lookup, e] using h
    simp only [resolve, dif_neg e]
    change Variable.there (resolve Δ x (inc x σ hh)) = Variable.there (ρ (resolve Γ x hh))
    exact congrArg Variable.there (hr x σ hh)

theorem namedRenamingErasure : NamedRenamingErasure := by
  intro Symbol arity Γ Δ τ t inc ρ hr
  induction t generalizing Δ with
  | var x h => exact congrArg Term.var (hr x _ h)
  | app f a ihf iha =>
    change Term.app (erase (namedRename f inc)) (erase (namedRename a inc)) = _
    rw [ihf _ inc ρ hr, iha _ inc ρ hr]
    rfl
  | lam x body ih =>
    change Term.lam (erase (namedRename body (liftInclusion inc x _))) = _
    rw [ih _ _ _ (lift_resolution inc ρ hr x _)]
    rfl
  | zeroC | succC | caseC | recC => rfl
  | ranked s args ih =>
    change Term.ranked s (fun i => erase (namedRename (args i) inc)) = _
    have he : (fun i => erase (namedRename (args i) inc)) =
        (fun i => (erase (args i)).rename ρ) := by funext i; exact ih i _ inc ρ hr
    rw [he]
    rfl

theorem namedRenamingFootprint : NamedRenamingFootprint := by
  intro Symbol arity Γ Δ τ t inc
  induction t generalizing Δ with
  | var => exact ⟨rfl, rfl, rfl⟩
  | app f a ihf iha =>
    obtain ⟨hsf, hvf, hdf⟩ := ihf Δ inc
    obtain ⟨hsa, hva, hda⟩ := iha Δ inc
    simp only [namedRename, namedSupport, namedOccurrences, namedDepth]
    exact ⟨congrArg (fun s => _ ∪ s) (congrArg₂ (· ∪ ·) hsf hsa),
      congrArg₂ List.append hvf hva, congrArg₂ max hdf hda⟩
  | lam x body ih =>
    obtain ⟨hs, hv, hd⟩ := ih _ (liftInclusion inc x _)
    exact ⟨congrArg (fun s => _ ∪ s) hs,
      congrArg (List.filter (fun v : Nat × Ty => v.1 != x)) hv, congrArg (fun n => n + 1) hd⟩
  | zeroC | succC | caseC | recC => exact ⟨rfl, rfl, rfl⟩
  | ranked s args ih =>
    have hs := fun i => (ih i Δ inc).1
    have hv := fun i => (ih i Δ inc).2.1
    have hd := fun i => (ih i Δ inc).2.2
    simp only [namedRename, namedSupport, namedOccurrences, namedDepth]
    constructor
    · congr 2; funext i; exact hs i
    constructor
    · congr 2; funext i; exact hv i
    · congr 1; funext i; exact hd i

private theorem weaken_resolution {Γ : Context} (x : Nat) (σ : Ty) (hx : lookup Γ x = none) :
    ResolutionAlong (weakenInclusion x σ hx) (Renaming.weaken (contextTypes Γ) σ) := by
  intro y τ hy
  have hne : y ≠ x := by intro e; subst y; rw [hx] at hy; cases hy
  simp only [resolve, dif_neg hne]
  rfl

theorem actualFreshWeakening : ActualFreshWeakening := by
  intro Symbol arity Γ σ
  let hx := (concreteFreshName Γ).1
  refine ⟨hx, ?_⟩
  intro τ t
  exact ⟨namedRenamingErasure Symbol arity Γ _ τ t _ _
    (weaken_resolution (freshName Γ) σ hx), namedRenamingFootprint Symbol arity Γ _ τ t _⟩

end LogicLineages.OrdinalComparison.Source.SourceNamedWeakeningProof
