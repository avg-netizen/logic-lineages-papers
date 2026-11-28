module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaApplicationComputabilityProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

/-! Proofs of the four proved rows frozen in
`Paper16AccessibilityMilestoneTypedRowsTargetsV2` (Fable B3, 27 November 2026).

* `exact_WindowNeutralFacts`: `exact_ConditionalInternalNeutralFacts` at the `arithmetic` field of
  the joined rules.
* `exact_WindowBetaApplication`: `exact_OpenApplicationComputabilityFromBeta` at the
  `arithmetic`, `applicationOutput` and `betaCases` fields.
* `exact_LambdaFactFromReducts`: arrow introduction, then the previous row at the two
  eigenvariables, with the instance premise transported along the composed renaming.
* `exact_TypedComputabilityFromRows`: excluded middle on the neutral test; the neutral branch is
  the neutral lemma applied to `NeutralReducts`; the other branch splits on the source type.

No new arithmetic. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowTypeApplicationRuleChecks (exact_ApplicationIntroduction)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalNeutralFactsTargets (D FactsAt atom direct reducts)
open NumberedWindowInternalNeutralFactsSyntaxProof (formulaRename reductsRename)
open NumberedWindowInternalNeutralFactsProof (exact_ConditionalInternalNeutralFacts)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource freeSource)
open NumberedWindowInternalLiteralBetaApplicationComputabilityProof
  (exact_OpenApplicationComputabilityFromBeta)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow TypedCarrierComputability)
open Paper16AccessibilityMilestoneTypedRowsTargetsV2

/-- Case split on an object formula. -/
private theorem byCases {body : PositiveArithmeticOperators.Positive (Fin 1)} {α : Type}
    {Γ : List (Formula α)} (test goal : Formula α)
    (yes : Nonempty (Derivation body (test :: Γ) goal))
    (no : Nonempty (Derivation body (test.not :: Γ) goal)) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨yes⟩ := yes
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle test)
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

/-- One more hypothesis. -/
private theorem addOne {body : PositiveArithmeticOperators.Positive (Fin 1)} {α : Type}
    {Γ : List (Formula α)} {f : Formula α} (extra : Formula α)
    (h : Nonempty (Derivation body Γ f)) : Nonempty (Derivation body (extra :: Γ) f) :=
  h.map (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp))

theorem exact_WindowNeutralFacts : WindowNeutralFacts := by
  intro S K W A L₀ U c joined τ
  exact exact_ConditionalInternalNeutralFacts joined.arithmetic τ

theorem exact_WindowBetaApplication : WindowBetaApplication := by
  intro S K W A L₀ U c joined σ τ α Γ x u t app earlier arg beta
  exact exact_OpenApplicationComputabilityFromBeta A.presentation (windowApp A) (windowHop A)
    L₀ A.least A.scalar neutralSource bottomSource freeSource U c joined.arithmetic
    joined.applicationOutput joined.betaCases σ τ x u t app earlier arg beta

theorem exact_LambdaFactFromReducts : LambdaFactFromReducts := by
  intro S K W A L₀ U c joined reductRow σ τ α Γ x held typed shape instances
  have lower := reductRow σ τ α Γ x held typed shape instances
  let data := A.presentation
  let p := windowApp A
  apply exact_ApplicationIntroduction (sourceBody data c) p σ τ α Γ x
  let j₁ : α → α ⊕ Fin 1 := Sum.inl
  let j₂ : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let j : α → (α ⊕ Fin 1) ⊕ Fin 1 := j₂ ∘ j₁
  let u : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let t : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let x' := x.relabel j
  let Acc := accepts p x' u t
  let Cu := formula p σ u
  let Δ := Cu :: Acc :: (Γ.map weaken).map weaken
  change D data c Δ (formula p τ t)
  have keep (f : Formula α) (hf : f ∈ Γ) : f.relabel j ∈ Δ := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    rw [← formulaRelabelComposition j₁ j₂]
    apply List.mem_map.mpr
    exact ⟨weaken f, List.mem_map.mpr ⟨f, hf, rfl⟩, rfl⟩
  have ee := renameInto lower j Δ keep
  rw [reductsRename] at ee
  have app : D data c Δ Acc :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have input : D data c Δ Cu := ⟨Derivation.hypothesis List.mem_cons_self⟩
  apply exact_WindowBetaApplication S K W A L₀ U c joined σ τ _ Δ x' u t app ee input
  intro β k Ω y retain step
  have e : x'.relabel k = x.relabel (k ∘ j) := Term.relabel_relabel j k x
  have a := renameInto app k Ω retain
  change D data c Ω ((accepts p x' u t).relabel k) at a
  rw [acceptsRename, e] at a
  have supply := renameInto input k Ω retain
  change D data c Ω ((formula p σ u).relabel k) at supply
  rw [formulaRename] at supply
  have keepBoth (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
    simpa only [formulaRelabelComposition] using retain _ (keep f hf)
  rw [e]
  exact instances β (k ∘ j) Ω (u.relabel k) (t.relabel k) y keepBoth supply a step

theorem exact_TypedComputabilityFromRows : TypedComputabilityFromRows := by
  intro S K W A L₀ U c guard joined neutralRow groundRow reductRow instanceRow τ hτ α Γ q held
    typed
  rw [guard]
  let test : Formula α := atom neutralSource q
  apply byCases test
  · have held' := addOne test held
    have typed' := addOne test typed
    have isNeutral : D A.presentation c (test :: Γ) test :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (exact_WindowNeutralFacts S K W A L₀ U c joined (formulaType τ)).neutral α
      (test :: Γ) q held' isNeutral (neutralRow τ hτ α (test :: Γ) q held' typed' isNeutral)
  · have held' := addOne test.not held
    have typed' := addOne test.not typed
    have notNeutral : D A.presentation c (test.not :: Γ) test.not :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    cases τ with
    | ground =>
      obtain ⟨no⟩ := groundRow α (test.not :: Γ) q held' typed' notNeutral
      exact ⟨Derivation.explosion no⟩
    | arrow σ ρ =>
      exact exact_LambdaFactFromReducts S K W A L₀ U c joined reductRow (formulaType σ)
        (formulaType ρ) α (test.not :: Γ) q held' typed' notNeutral
        (instanceRow σ ρ hτ α (test.not :: Γ) q held' typed' notNeutral)

#print axioms exact_WindowNeutralFacts
#print axioms exact_WindowBetaApplication
#print axioms exact_LambdaFactFromReducts
#print axioms exact_TypedComputabilityFromRows

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsProofV2
