module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshReportV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledFreshSelectionV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedTyped (chosenA)
open NumberedWindowInternalFreshProbeSyntaxProof (chosenRename freshInstantiate unaryRename)
open NumberedWindowInternalFreshProbeTargets (chosenAt)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar finiteCodes storedTypeIn)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions
  (addressScalar shapeChecks coordinateCall)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead chosenCell)
open NumberedWindowInternalSparsePathEnvelope (applyUnary run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt flagOfCell headTailOfCell)
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open Paper16AccessibilityMilestoneFreshReportV2 (exact_ChosenFreshFromReports)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (reinstallFreshScalar)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

attribute [local irreducible] programGraph

private theorem numeralReport {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 1) (n k : Nat) (fit : run p n = k) :
    Nonempty (Derivation body Γ (programGraph p (numeral k) ![numeral n])) := by
  have graph := exact_NumeralGraph 1 p (n ::ᵥ nil) body α Γ
  have inputs : NumberedWindowNumeralGraphTargets.inputs (n ::ᵥ nil) =
      (![numeral n] : Fin 1 → OTerm α) := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  change evaluate p (n ::ᵥ nil) = k at fit
  rw [inputs, fit] at graph
  exact graph

/-- Obtain the actual fresh successor from the installed carrier with its
literal scalar filter and a physical report for an arrow result. -/
theorem exact_ReinstalledFreshExists {S : Spine.Signature} {K : List Ty}
    (A : InstalledWindow S K (sourceWindow K)) (forming : Program 3)
    (shape : A.scalar = finiteScalar (addressScalar A.contextGuard A.typeGuard forming A.least)
      (finiteCodes (sourceWindow K)))
    (c : Nat) (σ τ : ProbeTy) {α : Type} {Γ : List (Formula α)} (q : OTerm α)
    (held : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (carrier A.presentation false c q)))
    (result : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph rawResult (numeral (typeCode (.arrow σ τ))) ![q]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (chosenAt (chosenA (reinstallFreshScalar A).probes) q)) := by
  let body := sourceBody A.presentation c
  let v := (reinstallFreshScalar A).probes
  let a := chosenA v
  let nameProgram := applyUnary v.freshBound rawLeast
  let base := addressScalar A.contextGuard A.typeGuard forming A.least
  let codes := finiteCodes (sourceWindow K)
  have scalar : Nonempty (Derivation body Γ (programGraph A.scalar (suc z) ![q])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body α Γ q).mp held
  have filtered : Nonempty (Derivation body Γ (programGraph (finiteScalar base codes) (suc z) ![q])) :=
    shape ▸ scalar
  obtain ⟨filter⟩ := conjunctionRecover base (storedTypeIn codes) ![q] filtered
  obtain ⟨checked⟩ := conjunctionRecover (shapeChecks A.contextGuard A.typeGuard)
    (coordinateCall forming A.least) ![q] ⟨Derivation.conjunctionLeft filter⟩
  obtain ⟨address⟩ := conjunctionRecover addressGood
    (ID1Completion.InternalAcceptance.conjunction
      (applyUnary A.contextGuard rawContext) (applyUnary A.typeGuard rawResult)) ![q]
    ⟨Derivation.conjunctionLeft checked⟩
  have addressHeld : Nonempty (Derivation body Γ (programGraph addressGood (suc z) ![q])) :=
    ⟨Derivation.conjunctionLeft address⟩
  let code := typeCode (.arrow σ τ)
  let t : OTerm α := numeral code
  have cell : chosenCell code = some (typeCode σ, typeCode τ) := cellAt (typeCode σ) (typeCode τ)
  have cellGoodAt : Nonempty (Derivation body Γ (programGraph cellGood (suc z) ![t])) :=
    numeralReport cellGood code 1 (flagOfCell cell)
  have cellHeadAt : Nonempty (Derivation body Γ (programGraph cellHead (numeral (typeCode σ)) ![t])) :=
    numeralReport cellHead code (typeCode σ) (headTailOfCell cell).1
  have arrow : Nonempty (Derivation body Γ (programGraph arrowGood (suc z) ![q])) := by
    unfold arrowGood applyUnary
    apply compositionValue cellGood (fun _ => rawResult) (suc z) ![q] ![t] cellGoodAt
    intro i
    obtain rfl := Fin.eq_zero i
    exact result
  have domain : Nonempty (Derivation body Γ (programGraph rawDomain (numeral (typeCode σ)) ![q])) := by
    unfold rawDomain applyUnary
    apply compositionValue cellHead (fun _ => rawResult) (numeral (typeCode σ)) ![q] ![t] cellHeadAt
    intro i
    obtain rfl := Fin.eq_zero i
    exact result
  apply programCases rawContext ![q] (chosenAt a q)
  intro β j Δ ctx keep ctxValue
  rw [chosenRename]
  rw [unaryRename] at ctxValue
  have scalar' := renameInto scalar j Δ keep
  have address' := renameInto addressHeld j Δ keep
  have arrow' := renameInto arrow j Δ keep
  have domain' := renameInto domain j Δ keep
  simp only [programRename, unaryRename, sucRelabel, zRelabel, numeralRename] at scalar' address' arrow' domain'
  apply programCases nameProgram ![q.relabel j] (chosenAt a (q.relabel j))
  intro γ k Ω name retained nameValue
  rw [chosenRename]
  rw [unaryRename] at nameValue
  have scalar'' := renameInto scalar' k Ω retained
  have address'' := renameInto address' k Ω retained
  have arrow'' := renameInto arrow' k Ω retained
  have domain'' := renameInto domain' k Ω retained
  have ctxValue' := renameInto ctxValue k Ω retained
  simp only [programRename, unaryRename, sucRelabel, zRelabel, numeralRename]
    at scalar'' address'' arrow'' domain'' ctxValue'
  let q' := (q.relabel j).relabel k
  let u := packedFreeTerm (ctx.relabel k) (numeral (typeCode σ)) name
  obtain ⟨fresh⟩ := exact_ChosenFreshFromReports v q' (ctx.relabel k) (numeral (typeCode σ)) name
    scalar'' address'' arrow'' ctxValue' domain'' nameValue
  unfold chosenAt
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb u)
  rw [freshInstantiate]
  exact fresh

#print axioms exact_ReinstalledFreshExists

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledFreshSelectionV2
