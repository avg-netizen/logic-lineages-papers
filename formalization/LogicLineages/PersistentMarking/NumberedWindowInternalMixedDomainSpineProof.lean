module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMixedDomainSpineProof
open FirstOrder Language LogicLineages.OrdinalComparison.Source LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (formula accepts)
open NumberedWindowInternalProbeTargets NumberedWindowTypeApplicationRuleChecks
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalPullbackTargets (Pullback)

/-- Each member of the right application spine may ask for either a
ground probe or an arbitrary (possibly higher domain) arrow into ground. -/
inductive ProbeDomain : Ty → Prop where
  | ground : ProbeDomain .ground
  | arrowGround (σ : Ty) : ProbeDomain (.arrow σ .ground)

/-- This restriction is a metalevel index for the existing object
formula and source types, not a replacement predicate interpretation. -/
inductive MixedDomains : Ty → Prop where
  | base : MixedDomains .ground
  | arrow {σ τ : Ty} : ProbeDomain σ → MixedDomains τ → MixedDomains (.arrow σ τ)

@[expose] def MixedFreshAt (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat) : Prop :=
  ∀ (σ τ : Ty), ProbeDomain σ → ∀ (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation (sourceBody d c) Γ (typedAt h (.arrow σ τ) q)) →
    Nonempty (Derivation (sourceBody d c) Γ (freshAt a q u)) →
    Nonempty (Derivation (sourceBody d c) Γ (formula p σ u))

private theorem formulaRename {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

private theorem carry {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    {φ : Formula α} (A : Formula (α ⊕ Fin 1)) (d : Nonempty (Derivation body Γ φ)) :
    Nonempty (Derivation body (A :: Γ.map weaken) (φ.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto d Sum.inl _ (fun a ha => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩))

/-- True object C→I in the mixed right spine. The fresh proof and the
typed closedness are on the same physical p/a/h; the function-side
backward accessibility cut is the independently provided Pullback. -/
theorem exact_MixedSpineTypedComputabilityImpliesMembership (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat)
    (pullback : Pullback d p c) (total : TypedProbeTotal d p h a c) (fresh : MixedFreshAt d p h a c) :
    ∀ (τ : Ty), MixedDomains τ → ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation (sourceBody d c) Γ (typedAt h τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (formula p τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (membership false q)) := by
  intro τ support
  induction support with
  | base =>
    intro α Γ q _ hC
    exact hC
  | @arrow σ τ permitted _ ih =>
    intro α Γ q ht hC
    obtain ⟨ex⟩ := total σ τ α Γ q ht
    let q' := q.relabel (Sum.inl : α → α ⊕ Fin 1)
    let q'' := q'.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
    let u : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
    let v : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
    let A := freshAt a q'' u ⊓ (accepts p q'' u v ⊓ typedAt h τ v)
    let E := existsOne A
    let Δ := E :: Γ.map weaken
    let Θ := A :: Δ.map weaken
    have typedQ := carry A (carry E ht)
    rw [typedRename,typedRename] at typedQ
    have computableQ := carry A (carry E hC)
    rw [formulaRename,formulaRename] at computableQ
    have pair : Derivation (sourceBody d c) Θ A := Derivation.hypothesis List.mem_cons_self
    have rest := Derivation.conjunctionRight pair
    have app := Derivation.conjunctionLeft rest
    have computableU := fresh σ τ permitted _ Θ q'' u typedQ ⟨Derivation.conjunctionLeft pair⟩
    have computableV := exact_ApplicationElimination (sourceBody d c) p σ τ _ Θ q'' u v
      computableQ ⟨app⟩ computableU
    have accessibleV := ih _ Θ v ⟨Derivation.conjunctionRight rest⟩ computableV
    obtain ⟨accessibleQ⟩ := pullback _ Θ q'' u v ⟨app⟩ accessibleV
    apply Nonempty.intro
    apply Derivation.existentialElimination ex
    change Derivation _ Δ ((membership false q).relabel Sum.inl)
    rw [membershipRename]
    apply Derivation.existentialElimination (Derivation.hypothesis (List.mem_cons_self : E ∈ Δ))
    change Derivation _ Θ ((membership false q').relabel Sum.inl)
    rw [membershipRename]
    exact accessibleQ


#print axioms exact_MixedSpineTypedComputabilityImpliesMembership
end LogicLineages.PersistentMarking.NumberedWindowInternalMixedDomainSpineProof
