module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedGroundSpineProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open NumberedWindowComputabilityFormulaTargets (formula accepts)
open NumberedWindowInternalProbeTargets NumberedWindowTypeApplicationRuleChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalGroundFreshTargets (GroundFreshAt)
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowInternalLiteralRefinedProbeProof (typedProbe groundFresh pullbackOfForward)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowGuardedGraphTargets (guard)
open NumberedWindowInternalPullbackTargets (ForwardRule Pullback)

/-- Actual source types in the ground-domain curried fragment. This restriction
is a theorem index, not a new object formula or a replacement code. -/
inductive GroundDomains : Ty → Prop where
  | base : GroundDomains .ground
  | arrow {τ : Ty} : GroundDomains τ → GroundDomains (.arrow .ground τ)

private theorem formulaRename {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

private theorem carry {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    {φ : Formula α} (A : Formula (α ⊕ Fin 1)) (d : Nonempty (Derivation body Γ φ)) :
    Nonempty (Derivation body (A :: Γ.map weaken) (φ.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto d Sum.inl _ (fun a ha => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩))

/-- Typed C→I in the actual curried ground-domain fragment, for arbitrary
open terms. Only the true function-side arithmetic image is abstracted by
the Pullback input of this reusable inference. -/
theorem groundSpine (d : Data) (p : Program 3) (h : Program 2) (a : Program 1) (c : Nat)
    (pullback : Pullback d p c) (total : TypedProbeTotal d p h a c) (fresh : GroundFreshAt d p h a c) :
    ∀ (τ : Ty), GroundDomains τ → ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
      Nonempty (Derivation (sourceBody d c) Γ (typedAt h τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (formula p τ q)) →
      Nonempty (Derivation (sourceBody d c) Γ (membership false q)) := by
  intro τ support
  induction support with
  | base =>
    intro α Γ q _ hC
    exact hC
  | @arrow τ _ ih =>
    intro α Γ q ht hC
    obtain ⟨ex⟩ := total .ground τ α Γ q ht
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
    have computableU := fresh τ _ Θ q'' u typedQ ⟨Derivation.conjunctionLeft pair⟩
    have computableV := exact_ApplicationElimination (sourceBody d c) p .ground τ _ Θ q'' u v
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


/-- The same physically refined literal body and actual parsed p/a/h. The only
unpaid arithmetic premise is the true same-body function-side forward rule. -/
theorem literalGroundSpine (i : Program 1) (r p : Program 3) (v : Inputs)
    (W : List ProbeTy) (closed : ChildClosed W) (exactGuard : v.applicationGuard = guard i p) (c : Nat)
    (forward : ForwardRule (refinedLiteral i r) v.applicationGuard c)
    (τ : Ty) (support : GroundDomains τ) (α : Type) (Γ : List (Formula α)) (q : OTerm α)
    (typed : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ (typedAt (chosenH v W) τ q)))
    (computable : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ
      (formula v.applicationGuard τ q))) :
    Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ (membership false q)) :=
  groundSpine _ _ _ _ c (pullbackOfForward i r p v exactGuard c forward)
    (typedProbe i r v W closed c) (groundFresh i r p v W closed exactGuard c) τ support α Γ q typed computable

#print axioms groundSpine
#print axioms literalGroundSpine
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedGroundSpineProof
