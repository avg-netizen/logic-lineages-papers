module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypedIntroductionV2
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

/-! Proofs of the frozen `Paper16AccessibilityMilestoneArrowTypingTargetsV2.StoredTypingFromReports`
and `TypingCasesFromReports` (Fable B, 27 November 2026).

Typing at the stored type goes by external recursion on the type. The ground case is the
introduction of `Paper16AccessibilityMilestoneGroundTypedIntroductionV2`. The arrow case opens the
fresh report and the supplied application result, types the result at the codomain by the
recursive call, and closes with `exact_OriginalArrowTypedIntroduction`. The type split is the
finite disjunction over the stored types of the window. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchObjectGraphProof (memberAt)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeSyntaxProof (freshRename unaryRename)
open NumberedWindowInternalFreshProbeTargets (chosenAt)
open NumberedWindowInternalProbeTargets (OTerm typeCode typedAt freshAt)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneArrowTypedIntroductionV2 (exact_OriginalArrowTypedIntroduction)
open Paper16AccessibilityMilestoneGroundTypedIntroductionV2 (exact_RequestedTypeTestFromResult)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2

/-- The acceptance formula is the graph of the same program at output one. -/
private theorem acceptsGraph {α : Type} (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f, u, y] := rfl

attribute [local irreducible] programGraph

private theorem storedRename {α β : Type} (τ : ProbeTy) (q : OTerm α) (j : α → β) :
    (storedType τ q).relabel j = storedType τ (q.relabel j) := by
  simp only [storedType, programRename, unaryRename, numeralRename]

/-- Elimination of the finite stored-type disjunction. -/
private theorem choicesElim {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (W : List ProbeTy) (q : OTerm α) (goal : Formula α)
    (choices : Nonempty (Derivation body Γ (storedTypeChoices W q)))
    (branches : ∀ ρ ∈ W, Nonempty (Derivation body Γ ((storedType ρ q).imp goal))) :
    Nonempty (Derivation body Γ goal) := by
  induction W generalizing Γ with
  | nil =>
    obtain ⟨impossible⟩ := choices
    have absurdity : Derivation body Γ ⊥ := impossible
    exact ⟨Derivation.explosion absurdity⟩
  | cons ρ rest ih =>
    obtain ⟨split⟩ := choices
    have split' : Derivation body Γ (storedType ρ q ⊔ storedTypeChoices rest q) := split
    obtain ⟨atHead⟩ := branches ρ List.mem_cons_self
    let R := storedTypeChoices rest q
    have later : Nonempty (Derivation body (R :: Γ) goal) := by
      apply ih (Γ := R :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro ρ' listed
      obtain ⟨branch⟩ := branches ρ' (List.mem_cons_of_mem _ listed)
      exact ⟨addHyp branch R⟩
    obtain ⟨later⟩ := later
    exact ⟨disjunctionElimination split' atHead (Derivation.implicationIntroduction later)⟩

variable {S : Spine.Signature} {K : List Ty}

/-- The ground branch of the selected checker from the listed ground type, the prior
checker and the zero result field. -/
private theorem groundIntroduction (A : InstalledWindow S K (sourceWindow K)) (c : Nat)
    (listed : (.ground : ProbeTy) ∈ sourceWindow K)
    {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (prior : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.priorTyped (suc z) ![z, q])))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult z ![q]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (typedAt (chosenH A.probes (sourceWindow K)) .ground q)) := by
  let body := sourceBody A.presentation c
  let leaves := chosenLeaves A.probes
  change Nonempty (Derivation body Γ
    (programGraph (dispatch leaves (sourceWindow K)) (suc z) ![z, q]))
  apply (memberAt leaves (sourceWindow K) .ground listed (suc z) q).mpr
  have request := exact_RequestedTypeTestFromResult z q result
  have base : Nonempty (Derivation body Γ (programGraph leaves.baseTyped (suc z) ![z, q])) := by
    change Nonempty (Derivation body Γ
      (programGraph (baseWithResult A.probes.priorTyped) (suc z) ![z, q]))
    rw [baseWithResult, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept A.probes.priorTyped requestedTypeTest ![z, q] prior request
  have zero : Nonempty (Derivation body Γ (programGraph (literal 1 0) z ![q])) := by
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 0 ![q]
  exact compositionValue leaves.baseTyped
    (Fin.cons (literal 1 0) (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))
    (suc z) ![q] ![z, q] base
    (fun i => Fin.cases zero
      (Fin.cases (projectionValue (0 : Fin 1) ![q]) (fun j => Fin.elim0 j)) i)

/-- Typing at the stored type, by recursion on the type. -/
theorem exact_StoredTypingFromReports (A : InstalledWindow S K (sourceWindow K)) (c : Nat) :
    StoredTypingFromReports A c := by
  intro reports total ρ
  induction ρ with
  | ground =>
    intro listed α Γ q held result
    have result' : Nonempty (Derivation (sourceBody A.presentation c) Γ
        (programGraph rawResult z ![q])) := result
    have prior := reports.priorIntro α Γ z q held result'
    exact groundIntroduction A c listed q prior result'
  | arrow σ τ _ ihτ =>
    intro listed α Γ q held result
    let body := sourceBody A.presentation c
    let W := sourceWindow K
    let h := chosenH A.probes W
    let a := chosenA A.probes
    let p := A.probes.applicationGuard
    have childListed : τ ∈ W := A.valid.2.1 σ τ listed
    obtain ⟨chosen⟩ := reports.freshIntro σ τ α Γ q held result
    let j : α → α ⊕ Fin 1 := Sum.inl
    let u : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    let φ : Formula (α ⊕ Fin 1) := freshAt a (q.relabel j) u
    let Δ : List (Formula (α ⊕ Fin 1)) := φ :: Γ.map weaken
    have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := fun f hf =>
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
    have inner : Nonempty (Derivation body Δ (weaken (typedAt h (.arrow σ τ) q))) := by
      change Nonempty (Derivation body Δ ((typedAt h (.arrow σ τ) q).relabel j))
      rw [typedRename]
      have held₁ := renameInto held j Δ keep
      rw [carrierRename] at held₁
      have result₁ := renameInto result j Δ keep
      rw [storedRename] at result₁
      have fresh₁ : Nonempty (Derivation body Δ (freshAt a (q.relabel j) u)) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨found⟩ := total σ τ listed (α ⊕ Fin 1) Δ (q.relabel j) u held₁ result₁ fresh₁
      let k : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
      let v : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
      let q₂ : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := (q.relabel j).relabel k
      let u₂ : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := u.relabel k
      let ψ : Formula ((α ⊕ Fin 1) ⊕ Fin 1) := accepts p q₂ u₂ v ⊓ storedType τ v
      let Ω : List (Formula ((α ⊕ Fin 1) ⊕ Fin 1)) := ψ :: Δ.map weaken
      have keep₂ : ∀ f ∈ Δ, f.relabel k ∈ Ω := fun f hf =>
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
      have found' : Derivation body Δ (existsOne ψ) := found
      have last : Nonempty (Derivation body Ω (weaken (typedAt h (.arrow σ τ) (q.relabel j)))) := by
        change Nonempty (Derivation body Ω ((typedAt h (.arrow σ τ) (q.relabel j)).relabel k))
        rw [typedRename]
        have held₂ := renameInto held₁ k Ω keep₂
        rw [carrierRename] at held₂
        have result₂ := renameInto result₁ k Ω keep₂
        rw [storedRename] at result₂
        have fresh₂ := renameInto fresh₁ k Ω keep₂
        rw [freshRename] at fresh₂
        have both : Derivation body Ω ψ := Derivation.hypothesis List.mem_cons_self
        have app : Nonempty (Derivation body Ω (accepts p q₂ u₂ v)) :=
          ⟨Derivation.conjunctionLeft both⟩
        have typedV : Nonempty (Derivation body Ω (storedType τ v)) :=
          ⟨Derivation.conjunctionRight both⟩
        have carrierV := reports.resultCarrier ((α ⊕ Fin 1) ⊕ Fin 1) Ω q₂ u₂ v app
        have codomain := ihτ childListed ((α ⊕ Fin 1) ⊕ Fin 1) Ω v carrierV typedV
        have prior := reports.priorIntro ((α ⊕ Fin 1) ⊕ Fin 1) Ω
          (numeral (typeCode (.arrow σ τ))) q₂ held₂ result₂
        have optionApp := reports.optionIntro ((α ⊕ Fin 1) ⊕ Fin 1) Ω q₂ u₂ v app
        have app' : Nonempty (Derivation body Ω (programGraph p (suc z) ![q₂, u₂, v])) := by
          rw [← acceptsGraph]
          exact app
        exact exact_OriginalArrowTypedIntroduction A c σ τ listed q₂ u₂ v prior result₂ fresh₂
          optionApp app' codomain
      obtain ⟨last⟩ := last
      exact ⟨Derivation.existentialElimination found' last⟩
    obtain ⟨inner⟩ := inner
    have chosen' : Derivation body Γ (existsOne φ) := chosen
    exact ⟨Derivation.existentialElimination chosen' inner⟩

/-- The type split of the milestone from the probe reports and the fresh application. -/
theorem exact_TypingCasesFromReports (A : InstalledWindow S K (sourceWindow K)) (c : Nat) :
    TypingCasesFromReports A c := by
  intro reports total α Γ q goal held branches
  let body := sourceBody A.presentation c
  have typing := exact_StoredTypingFromReports A c reports total
  apply choicesElim (sourceWindow K) q goal (reports.storedListed α Γ q held)
  intro ρ listed
  obtain ⟨τ₀, hτ₀, same⟩ := List.mem_map.mp listed
  subst same
  obtain ⟨branch⟩ := branches τ₀ hτ₀
  obtain ⟨heldProof⟩ := held
  let stored := storedType (formulaType τ₀) q
  obtain ⟨typed⟩ := typing (formulaType τ₀) listed α (stored :: Γ) q ⟨addHyp heldProof stored⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step : Derivation body Γ
      ((typedAt (chosenH A.probes (sourceWindow K)) (formulaType τ₀) q).imp goal) :=
    Derivation.implicationIntroduction branch
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp step stored) typed)⟩

#print axioms exact_StoredTypingFromReports
#print axioms exact_TypingCasesFromReports

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingProofV2
