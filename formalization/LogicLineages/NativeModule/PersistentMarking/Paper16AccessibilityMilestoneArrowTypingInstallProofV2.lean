module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledFreshSelectionV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneGroundTypedIntroductionV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2.StackedLiteralProbeReports`
(Fable B, 27 November 2026).

Each of the five reports is one of the checked open laws of 26 November read on the stacked
window: the finite scalar filter with the literal membership choices, the prior checker built
from the scalar and the result-field test, `exact_ReinstalledFreshExists`,
`exact_ReinstalledOptionApplicationReport`, and the supplied result carrier. The only new
derivation turns the literal code choices of the reported result field into stored-type
choices over the window. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCheckerCoordinates (domain)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalFreshProbeDispatchControlChecks
  (exact_DispatchControlAST exact_DispatchObjectTypeCode)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped (requestedTypeTest)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFiniteScalarGuardProof
  (finiteCodes finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipSupportProof (memberToChoices)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalChoices)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowProbeCode (code)
open Paper16AccessibilityMilestoneGroundTypedIntroductionV2 (exact_RequestedTypeTestFromResult)
open Paper16AccessibilityMilestoneInstalledFreshSelectionV2 (exact_ReinstalledFreshExists)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (priorTypedOf retypeWindow reinstallFreshScalar)
open Paper16AccessibilityMilestoneOptionReinstallV2 (exact_ReinstalledOptionApplicationReport)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2

/-- The acceptance formula is the graph of the same program at output one. -/
private theorem acceptsGraph {α : Type} (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f, u, y] := rfl

attribute [local irreducible] programGraph

private theorem storedRename {α β : Type} (τ : ProbeTy) (q : OTerm α) (j : α → β) :
    (storedType τ q).relabel j = storedType τ (q.relabel j) := by
  simp only [storedType, programRename, unaryRename, numeralRename]

private theorem choicesRename {α β : Type} (W : List ProbeTy) (q : OTerm α) (j : α → β) :
    (storedTypeChoices W q).relabel j = storedTypeChoices W (q.relabel j) := by
  induction W with
  | nil => rfl
  | cons ρ rest ih =>
    change ((storedType ρ q).relabel j ⊔ (storedTypeChoices rest q).relabel j) = _
    rw [storedRename, ih]
    rfl

/-- Literal code choices for the reported result field give stored-type choices. -/
private theorem codesToStored {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (W : List ProbeTy) (q ty : OTerm α)
    (reported : Nonempty (Derivation body Γ (programGraph rawResult ty ![q])))
    (choices : Nonempty (Derivation body Γ (literalChoices (finiteCodes W) ty))) :
    Nonempty (Derivation body Γ (storedTypeChoices W q)) := by
  induction W generalizing Γ with
  | nil =>
    obtain ⟨impossible⟩ := choices
    have absurdity : Derivation body Γ ⊥ := impossible
    exact ⟨Derivation.explosion absurdity⟩
  | cons ρ rest ih =>
    obtain ⟨split⟩ := choices
    obtain ⟨reportedProof⟩ := reported
    let P := eqn ty (numeral (code ρ))
    let Q := literalChoices (finiteCodes rest) ty
    have split' : Derivation body Γ (P ⊔ Q) := split
    have moved : Nonempty (Derivation body (P :: Γ)
        (programGraph rawResult (numeral (code ρ)) ![q])) :=
      outputTransport rawResult ty (numeral (code ρ)) ![q]
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp reportedProof P⟩
    rw [exact_DispatchObjectTypeCode ρ] at moved
    obtain ⟨moved⟩ := moved
    have stored : Derivation body (P :: Γ) (storedType ρ q) := moved
    have atHead : Derivation body Γ (P.imp (storedTypeChoices (ρ :: rest) q)) :=
      Derivation.implicationIntroduction (orLeft stored)
    obtain ⟨later⟩ := ih (Γ := Q :: Γ) ⟨addHyp reportedProof Q⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have atTail : Derivation body Γ (Q.imp (storedTypeChoices (ρ :: rest) q)) :=
      Derivation.implicationIntroduction (orRight later)
    exact ⟨disjunctionElimination split' atHead atTail⟩

variable {S : Spine.Signature} {K : List Ty}

/-- A carrier address under the finite scalar filter stores one of the window's types. -/
private theorem storedChoicesOfCarrier (A : InstalledWindow S K (sourceWindow K)) (base : Program 1)
    (shape : A.scalar = finiteScalar base (finiteCodes (sourceWindow K))) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (held : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (carrier A.presentation false c q))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (storedTypeChoices (sourceWindow K) q)) := by
  let body := sourceBody A.presentation c
  apply programCases rawResult ![q] (storedTypeChoices (sourceWindow K) q)
  intro β j Δ ty includes reported
  rw [choicesRename]
  rw [unaryRename] at reported
  have held' := renameInto held j Δ includes
  rw [carrierRename] at held'
  have accepted : Nonempty (Derivation body Δ (programGraph A.scalar (suc z) ![q.relabel j])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body β Δ (q.relabel j)).mp held'
  rw [shape] at accepted
  have listed := (exact_OpenLiteralFiniteScalar base (finiteCodes (sourceWindow K))
    (q.relabel j) ty reported accepted).2
  exact codesToStored (sourceWindow K) (q.relabel j) ty reported
    (memberToChoices (finiteCodes (sourceWindow K)) ty listed)

/-- The prior checker built from the installed scalar accepts a carrier address at its
reported result field. -/
private theorem priorOfCarrier (A : InstalledWindow S K (sourceWindow K)) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (t q : OTerm α)
    (held : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (carrier A.presentation false c q)))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult t ![q]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph (priorTypedOf A.scalar) (suc z) ![t, q])) := by
  let body := sourceBody A.presentation c
  have rawCarrier : Nonempty (Derivation body Γ (programGraph A.scalar (suc z) ![q])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body α Γ q).mp held
  have lifted : Nonempty (Derivation body Γ (programGraph (domain A.scalar) (suc z) ![t, q])) := by
    unfold domain
    apply compositionValue A.scalar (fun _ => .projection (1 : Fin 2))
      (suc z) ![t, q] ![q] rawCarrier
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (1 : Fin 2) ![t, q]
  have request := exact_RequestedTypeTestFromResult t q result
  have prior : Nonempty (Derivation body Γ (programGraph (priorTypedOf A.scalar) (suc z) ![t, q])) := by
    rw [priorTypedOf, exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept (domain A.scalar) requestedTypeTest ![t, q] lifted request
  exact prior

/-- The five open reports on the window with the literal probe leaves. -/
theorem exact_StackedLiteralProbeReports : StackedLiteralProbeReports := by
  intro S K A forming shape core c output
  exact
    { storedListed := fun α Γ q held => storedChoicesOfCarrier A _ shape c q held
      priorIntro := fun α Γ t q held result => priorOfCarrier A c t q held result
      freshIntro := fun σ τ α Γ q held result =>
        exact_ReinstalledFreshExists (retypeWindow A) forming shape c σ τ q held result
      optionIntro := fun α Γ q u v accepted => by
        rw [acceptsGraph] at accepted
        exact exact_ReinstalledOptionApplicationReport (reinstallFreshScalar (retypeWindow A)) c
          core q u v accepted
      resultCarrier := fun α Γ x u t app => output α Γ x u t app }

#print axioms exact_StackedLiteralProbeReports

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallProofV2
