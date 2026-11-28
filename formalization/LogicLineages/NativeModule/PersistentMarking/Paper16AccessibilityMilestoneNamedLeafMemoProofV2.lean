module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureDispatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredAuxWindowIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

/-! Proofs of the four frozen laws of
`Paper16AccessibilityMilestoneNamedLeafMemoTargetsV2` (Fable B2, 27 November 2026).

Each is a row of a memo recursion at a key that is not an auxiliary node. The patterns are the
accepted ones: `exact_OpenCoverAuxSyntaxIntro` (selected unary memo, introduction),
`exact_OpenCoverNamedLeafSharedMeasure` (selected unary memo, elimination),
`exact_OpenCoverInstallNonAuxWindow` and `exact_OpenCoveredAuxWindowIntro` (context memo). -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchIntro successorBranchIntro zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue successorValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans addZero addSucc congSuc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF addRelabel)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalPairing (pairing)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
  (unaryRename rawConsRename packedBodyRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate certain measureAt shapeCheck)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph contextTable contextStep)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate strictAuxPositive)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate auxSyntax auxAccept)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafMeasureTargets
  (namedPrior namedMeasureBase namedMeasurePair)
open NumberedWindowInternalCoverNamedLeafMeasureDispatchProof
  (exact_OpenCoverNamedLeafMeasureDispatch)
open NumberedWindowInternalCoverSharedMemoTargets (ObservedStep)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
  (exact_OpenSelectedGrammarNamedLeafScratch)
open NumberedWindowInternalLiteralSyntaxMemoWindow (update syntaxAtKey)
open NumberedWindowInternalLiteralCoveredMemo
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open Paper16AccessibilityMilestoneNamedLeafMemoTargetsV2

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (b : Bool) (ty i : OTerm α) (j : α → β) :
    (namedPrior b ty i).relabel j = namedPrior b (ty.relabel j) (i.relabel j) := by
  have pairTermRename (x y : OTerm α) :
      (pairTerm x y).relabel j = pairTerm (x.relabel j) (y.relabel j) := by
    simp only [pairTerm, addRelabel, mulRelabel]
  simp only [namedPrior, pairTermRename, packedBodyRename, numeralRename, List.map_cons,
    List.map_nil]

private theorem namedRename {β : Type} (tag : Nat) (ty i : OTerm α) (j : α → β) :
    (namedTerm tag ty i).relabel j = namedTerm tag (ty.relabel j) (i.relabel j) := by
  simp only [namedTerm, rawConsRename, numeralRename, zRelabel]

private theorem selfWeak (i : OTerm α) : Nonempty (Derivation body Γ (ltF i (suc i))) := by
  apply actualOriginalOrderIntroduction body α Γ i (suc i) z
  rw [onEquality]
  exact ⟨trans (addSucc i z) (congSuc (addZero i))⟩

/-- The current key of the memo tape at a free-variable leaf. -/
private theorem leafKey (ty i old ctx : OTerm α) :
    Nonempty (Derivation body Γ (programGraph currentKey (namedTerm 0 ty i)
      ![namedPrior false ty i, old, ctx, z])) :=
  unaryGraph .succ (.projection 0) (namedTerm 0 ty i) (namedPrior false ty i)
    ![namedPrior false ty i, old, ctx, z] (successorValue ![namedPrior false ty i])
    (projectionValue 0 ![namedPrior false ty i, old, ctx, z])

/-! Syntax memo. -/

private theorem syntaxWithTable (V TV : Program 1) (ty i old : OTerm α)
    (valid : Nonempty (Derivation body Γ (programGraph V (suc z) ![namedTerm 0 ty i])))
    (table : Nonempty (Derivation body Γ (programGraph
      (scratchTable (constantZero 2) (auxSyntaxUpdate V TV)) old ![namedPrior false ty i, z, z]))) :
    Nonempty (Derivation body Γ (programGraph (auxSyntax V TV) (suc z) ![namedTerm 0 ty i])) := by
  let R : Program 4 := auxSyntaxUpdate V TV
  let prior := namedPrior false ty i
  let raw := namedTerm 0 ty i
  let xs : Fin 4 → OTerm α := ![prior, old, z, z]
  have reports := exact_OpenCoverNamedLeafMeasureDispatch false body α Γ ty i old
  have atKey : Nonempty (Derivation body Γ (programGraph (unaryAfter V currentKey) (suc z) xs)) :=
    unaryGraph V currentKey (suc z) raw xs valid (leafKey ty i old z)
  have step : Nonempty (Derivation body Γ (programGraph R (suc z) xs)) :=
    zeroBranchIntro certain (unaryAfter V currentKey) (auxAccept TV) (suc z) xs reports.2.1 atKey
  have installed := exact_OpenSelectedMemoSuccessor R body α Γ (suc z) prior old table step
  exact (projection R (suc z) raw).mpr installed

theorem exact_NamedLeafUnitSyntax : NamedLeafUnitSyntax := by
  intro V TV body α Γ ty i valid
  have inner : Nonempty (Derivation body Γ
      (programGraph (auxSyntax V TV) (suc z) ![namedTerm 0 ty i])) := by
    apply programCases (scratchTable (constantZero 2) (auxSyntaxUpdate V TV))
      ![namedPrior false ty i, z, z] _
    intro β j Δ old keep table
    simp only [tripleInputsRename, priorRename, zRelabel] at table
    have valid' := renameInto valid j Δ keep
    simp only [unaryRename, sucRelabel, zRelabel, namedRename] at valid'
    simp only [programRename, unaryInputsRename, sucRelabel, zRelabel, namedRename]
    exact syntaxWithTable V TV (ty.relabel j) (i.relabel j) old valid' table
  exact normalizeAccept (auxSyntax V TV) ![namedTerm 0 ty i] inner

/-! Measure memo. -/

private theorem measureFromRow (M : Program 1) (ty i old p : OTerm α)
    (row : ObservedStep (measureUpdate (namedMeasureBase M) chosenCombine)
      body Γ (namedPrior false ty i) old p) :
    Nonempty (Derivation body Γ (codePair p (suc z) i)) := by
  let B := namedMeasureBase M
  let raw := namedTerm 0 ty i
  let prior := namedPrior false ty i
  let xs : Fin 4 → OTerm α := ![prior, old, z, z]
  have reports := exact_OpenCoverNamedLeafMeasureDispatch false body α Γ ty i old
  have base := zeroBranchElim certain (unaryAfter B currentKey)
    (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p xs reports.2.1 row.update
  have actual : Nonempty (Derivation body Γ (programGraph B p ![raw])) := by
    apply compositionRecover B (fun _ : Fin 1 => currentKey) p xs ![raw] base
    intro k
    obtain rfl := Fin.eq_zero k
    exact leafKey ty i old z
  have pairReport : Nonempty (Derivation body Γ (programGraph namedMeasurePair p ![raw])) :=
    successorBranchElim (header 0 2) (branch (header 1 2) M namedMeasurePair)
      namedMeasurePair p z ![raw] reports.2.2.2.1 actual
  apply compositionRecover pairing ![literal 1 1, field 1] p ![raw] ![suc z, i] pairReport
  intro k
  exact Fin.cases (literalGraph 1 ![raw]) (Fin.cases reports.2.2.2.2.1 (fun l => Fin.elim0 l)) k

theorem exact_NamedLeafChosenMeasure : NamedLeafChosenMeasure := by
  intro M body α Γ ty i p actual
  apply exact_OpenCoverSharedMemoRowCases (measureUpdate (namedMeasureBase M) chosenCombine)
    body α Γ (namedPrior false ty i) p _ actual
  intro β j Δ old keep row
  simp only [pairRename, sucRelabel, zRelabel]
  rw [priorRename] at row
  exact measureFromRow M (ty.relabel j) (i.relabel j) old (p.relabel j) row

/-! Own cover. -/

theorem exact_NamedLeafOwnCover : NamedLeafOwnCover := by
  intro V TV M s body α Γ ty i vertices member valid held
  apply programCases (chosenMeasure (namedMeasureBase M)) ![namedTerm 0 ty i] _
  intro β j Δ p keep measured
  simp only [unaryInputsRename, namedRename] at measured
  have member' := renameInto member j Δ keep
  simp only [graphRename, typesTerm, numeralRename] at member'
  have valid' := renameInto valid j Δ keep
  simp only [unaryRename, sucRelabel, zRelabel, namedRename] at valid'
  have held' := renameInto held j Δ keep
  simp only [unaryRename, namedRename] at held'
  simp only [graphRename, namedRename]
  have measured' : Nonempty (Derivation body Δ (unary (chosenMeasure (namedMeasureBase M)) p
      (namedTerm 0 (ty.relabel j) (i.relabel j)))) := measured
  have pair := exact_NamedLeafChosenMeasure M body β Δ (ty.relabel j) (i.relabel j) p measured'
  exact exact_OpenSelectedGrammarNamedLeafScratch false (unitAuxSyntax V TV)
    (chosenMeasure (namedMeasureBase M)) s body β Δ p z (i.relabel j) (vertices.relabel j)
    (ty.relabel j) (i.relabel j) member' (selfWeak (i.relabel j)) valid' measured' pair held'

/-! Covered memo window. -/

private theorem coveredWithTable (C : Program 3) (s : Settings) (A : Program 2) (T V : Program 1)
    (ctx prior result old : OTerm α)
    (shape : Nonempty (Derivation body Γ (unary termShape z (suc prior))))
    (actual : Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx, suc prior])))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (suc prior))))
    (coverage : Nonempty (Derivation body Γ (coverageReport C s ctx (suc prior))))
    (table : Nonempty (Derivation body Γ (contextTable (coveredUpdate C s A T V) old prior ctx))) :
    Nonempty (Derivation body Γ
      (windowGraph (coveredMemoWindow C s A T V) ctx result (suc prior))) := by
  let R := coveredUpdate C s A T V
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior, old, ctx, z]
  let verifier := conjunction contextPresent (ownSeed C s)
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have noAux := unaryGraph termShape currentKey z raw xs shape key
  have leaf := binaryGraph A (.projection 2) currentKey (suc result) ctx raw xs actual
    (projectionValue 2 xs) key
  have strict : Nonempty (Derivation body Γ (programGraph (strictAuxUpdate A T) (suc result) xs)) :=
    zeroBranchIntro shapeCheck (binaryAfter A (.projection 2) currentKey) (strictAuxPositive T)
      (suc result) xs noAux leaf
  have atKey : Nonempty (Derivation body Γ (programGraph (syntaxAtKey V) (suc z) xs)) :=
    unaryGraph V currentKey (suc z) raw xs valid key
  have syntaxPaid : Nonempty (Derivation body Γ (programGraph (update A T V) (suc result) xs)) :=
    successorBranchIntro (normalize (syntaxAtKey V)) (constantZero 4) (strictAuxUpdate A T)
      (suc result) z xs (normalizeAccept (syntaxAtKey V) xs atKey) strict
  have covered : Nonempty (Derivation body Γ (programGraph (coverageAtKey C s) (suc z) xs)) := by
    apply compositionValue verifier ![.projection 2, constantZero 4, currentKey] (suc z) xs
      ![ctx, z, raw] coverage
    exact fun k => Fin.cases (projectionValue 2 xs)
      (Fin.cases (zeroConstantValue xs) (Fin.cases key (fun n => Fin.elim0 n))) k
  have step : Nonempty (Derivation body Γ (contextStep R (suc result) prior old ctx)) :=
    successorBranchIntro (normalize (coverageAtKey C s)) (constantZero 4) (update A T V)
      (suc result) z xs (normalizeAccept (coverageAtKey C s) xs covered) syntaxPaid
  have row := exact_OpenContextMemoSuccessor R body α Γ (suc result) prior old ctx table step
  have selected := (sameContext R (suc result) ctx raw).mpr row
  exact (exact_OpenIntrinsicQuery (coveredIntrinsic C s A T V) body α Γ ctx result raw).mpr selected

theorem exact_NonAuxCoveredWindow : NonAuxCoveredWindow := by
  intro C s A T V body α Γ ctx prior result shape actual valid coverage
  let R := coveredUpdate C s A T V
  let Q := windowGraph (coveredMemoWindow C s A T V) ctx result (suc prior)
  apply programCases (scratchTable (constantZero 2) R) ![prior, ctx, z] Q
  intro β j Δ old keep table
  simp only [tripleInputsRename, zRelabel] at table
  have shape' := renameInto shape j Δ keep
  have actual' := renameInto actual j Δ keep
  have valid' := renameInto valid j Δ keep
  have coverage' := renameInto coverage j Δ keep
  simp only [unaryRename, zRelabel, sucRelabel] at shape' valid'
  simp only [programRename, binaryInputsRename, sucRelabel] at actual'
  simp only [coverageReport, programRename, tripleInputsRename, sucRelabel, zRelabel] at coverage'
  simp only [Q, windowGraph, programRename, tripleInputsRename, sucRelabel, zRelabel]
  exact coveredWithTable C s A T V (ctx.relabel j) (prior.relabel j) (result.relabel j) old
    shape' actual' valid' coverage' table

#print axioms exact_NamedLeafUnitSyntax
#print axioms exact_NamedLeafChosenMeasure
#print axioms exact_NamedLeafOwnCover
#print axioms exact_NonAuxCoveredWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoProofV2
