module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDownwardChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb)
open ID1Completion.InternalSourceIntroductionSyntaxProof (termRelabelAsSubst formulaRelabelAsSubst)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets NumberedWindowInternalDownwardTargets
open NumberedWindowTypeApplicationRuleChecks

private theorem formulaRename {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

private theorem edgeRename {α β : Type} (d : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge d false c x y).relabel j = edge d false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge d false c x y).subst (fun a => emb (.var (j a))) = _
  rw [ID1Completion.InternalAccessibilityRulesSyntaxProof.edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

private theorem carry {α : Type} {body : PositiveArithmeticOperators.Positive (Fin 1)}
    {Γ : List (Formula α)} {φ : Formula α} (h : Nonempty (Derivation body Γ φ)) :
    Nonempty (Derivation body (Γ.map weaken) (φ.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto h Sum.inl _ (fun t ht => List.mem_map.mpr ⟨t,ht,rfl⟩)

private theorem transfer (d : Data) (p : Program 3) (c : Nat) (σ τ : Ty)
    (matchEdge : ApplicationEdgeMatching d p c)
    (ih : ∀ (β : Type) (Δ : List (Formula β)) (x y : OTerm β),
      Nonempty (Derivation (sourceBody d c) Δ (formula p τ x)) →
      Nonempty (Derivation (sourceBody d c) Δ (edge d false c x y)) →
      Nonempty (Derivation (sourceBody d c) Δ (formula p τ y)))
    {α : Type} {Γ : List (Formula α)} (f g u v : OTerm α)
    (hf : Nonempty (Derivation (sourceBody d c) Γ (formula p (.arrow σ τ) f)))
    (hr : Nonempty (Derivation (sourceBody d c) Γ (edge d false c f g)))
    (ha : Nonempty (Derivation (sourceBody d c) Γ (accepts p g u v)))
    (hu : Nonempty (Derivation (sourceBody d c) Γ (formula p σ u))) :
    Nonempty (Derivation (sourceBody d c) Γ (formula p τ v)) := by
  obtain ⟨existsEarlier⟩ := matchEdge α Γ f g u v hr ha
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := accepts p (f.relabel Sum.inl) (u.relabel Sum.inl) w ⊓ edge d false c w (v.relabel Sum.inl)
  let Δ := A :: Γ.map weaken
  have includeΓ (a : Formula α) (ha : a ∈ Γ) : a.relabel Sum.inl ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hf' := renameInto hf Sum.inl Δ includeΓ
  have hu' := renameInto hu Sum.inl Δ includeΓ
  rw [formulaRename] at hf' hu'
  have pair : Derivation (sourceBody d c) Δ A := Derivation.hypothesis List.mem_cons_self
  have hEarlier := exact_ApplicationElimination (sourceBody d c) p σ τ _ Δ _ _ w hf'
    ⟨Derivation.conjunctionLeft pair⟩ hu'
  obtain ⟨later⟩ := ih _ Δ w (v.relabel Sum.inl) hEarlier ⟨Derivation.conjunctionRight pair⟩
  apply Nonempty.intro
  apply Derivation.existentialElimination existsEarlier
  change Derivation _ Δ ((formula p τ v).relabel Sum.inl)
  rw [formulaRename]
  exact later

theorem exact_ComputabilityDownward : ComputabilityDownward := by
  intro d p c matchEdge τ
  induction τ with
  | ground =>
    intro α Γ f g hf hr
    exact ID1Completion.InternalAccessibilityRulesProof.actualOriginalSuccessorClosure
      d false c α Γ f g hf hr
  | arrow σ τ _ ih =>
    intro α Γ f g hf hr
    apply exact_ApplicationIntroduction (sourceBody d c) p σ τ α Γ g
    let u : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
    let v : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
    let j : α → (α ⊕ Fin 1) ⊕ Fin 1 := fun i => .inl (.inl i)
    let Δ := formula p σ u :: accepts p (g.relabel j) u v :: (Γ.map weaken).map weaken
    have hi (a : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (ha : a ∈ (Γ.map weaken).map weaken) : a ∈ Δ :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)
    obtain ⟨hf'⟩ := carry (carry hf)
    obtain ⟨hr'⟩ := carry (carry hr)
    simp only [formulaRename,Term.relabel_relabel] at hf'
    simp only [edgeRename,Term.relabel_relabel] at hr'
    exact transfer d p c σ τ matchEdge ih (Γ := Δ) (f.relabel j) (g.relabel j) u v
      ⟨Derivation.weakening hi hf'⟩ ⟨Derivation.weakening hi hr'⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

#print axioms exact_ComputabilityDownward
end LogicLineages.PersistentMarking.NumberedWindowInternalDownwardChecks
