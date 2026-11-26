module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks
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

private theorem numeralRename {α β : Type} (n : Nat) (j : α → β) :
    (numeral n : OTerm α).relabel j = numeral n := by
  induction n with
  | zero => exact zRelabel j
  | succ n ih => simpa only [numeral,sucRelabel] using congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem typedRename {α β : Type} (h : Program 2) (τ : Ty) (q : OTerm α) (j : α → β) :
    (typedAt h τ q).relabel j = typedAt h τ (q.relabel j) := by
  simp only [typedAt,ID1Completion.InternalControlGraphSupportProof.programRename,numeralRename]
  congr 1
  funext k
  refine Fin.cases ?_ (Fin.cases ?_ (fun b => Fin.elim0 b)) k
  · exact numeralRename _ _
  · rfl

private theorem formulaRename {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

private theorem carry {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    {φ : Formula α} (A : Formula (α ⊕ Fin 1)) (d : Nonempty (Derivation body Γ φ)) :
    Nonempty (Derivation body (A :: Γ.map weaken) (φ.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto d Sum.inl _ (fun a ha => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩))

theorem exact_TypedComputabilityImpliesMembership : TypedComputabilityImpliesMembership := by
  intro d p h a c pullback total fresh τ
  induction τ with
  | ground =>
    intro α Γ q _ hC
    exact hC
  | arrow σ τ _ ih =>
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
    have computableU := fresh σ τ _ Θ q'' u typedQ ⟨Derivation.conjunctionLeft pair⟩
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

#print axioms exact_TypedComputabilityImpliesMembership
end LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks
