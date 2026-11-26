module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoLiftGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenEvaluationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableChecks (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalAuxExchangeMemoLiftGapProof (pairRelabel)
open NumberedWindowInternalAuxMeasureStepTargets
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureOpenTargets
open NumberedWindowInternalAuxMeasureOpenDataProof
open NumberedWindowInternalAuxMeasureOpenSlotProof (slotReports)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem measureRename {β : Type} (base : Program 1) (P : Program 2) (out raw : OTerm α) (j : α → β) :
    (measureGraph base P out raw).relabel j = measureGraph base P (out.relabel j) (raw.relabel j) := by
  simp only [measureGraph,programRename,unaryInputsRename]

theorem deriveValue (base : Program 1) (P : Program 2) (dom cod fn arg mf ma out : OTerm α)
    (fnMeasure : Nonempty (Derivation body Γ (measureGraph base P mf fn)))
    (argMeasure : Nonempty (Derivation body Γ (measureGraph base P ma arg)))
    (combineGraph : Nonempty (Derivation body Γ (programGraph P out ![mf,ma]))) :
    Nonempty (Derivation body Γ (measureGraph base P out (auxiliaryTerm dom cod fn arg))) := by
  let R := measureUpdate base P
  apply programCases (scratchTable (constantZero 2) R) ![priorKey dom cod fn arg,z,z] _
  intro β j Δ old hJ table
  simp only [measureRename,auxiliaryRename]
  simp only [tripleInputsRename,zRelabel,priorKey,pairRelabel,packedBodyRename,numeralRename,List.map_cons,List.map_nil] at table
  have source := renameInto fnMeasure j Δ hJ
  have fixed := renameInto argMeasure j Δ hJ
  have counts := renameInto combineGraph j Δ hJ
  simp only [measureRename] at source fixed
  simp only [programRename,binaryInputsRename] at counts
  let fn' := fn.relabel j
  let arg' := arg.relabel j
  let d := dom.relabel j
  let c := cod.relabel j
  let prior := priorKey d c fn' arg'
  let xs : Fin 4 → OTerm β := ![prior,old,z,z]
  have fields := nodeReports (body := body) (Γ := Δ) d c fn' arg' old
  have earlier := bothChildBounds (body := body) (Γ := Δ) d c fn' arg'
  have fnRow := (projection R (mf.relabel j) fn').mp source
  have argRow := (projection R (ma.relabel j) arg').mp fixed
  have fnReports := slotReports R 2 fn' (mf.relabel j) prior old fields.key fields.fnField earlier.1 fnRow table
  have argReports := slotReports R 3 arg' (ma.relabel j) prior old fields.key fields.argField earlier.2 argRow table
  have enough : Nonempty (Derivation body Δ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck _ xs fields.shape
      (conjunctionAccept (earlierAt 2) (earlierAt 3) xs fnReports.1 argReports.1)
  have computed := binaryGraph P (measureAt 2) (measureAt 3) (out.relabel j) (mf.relabel j) (ma.relabel j)
    xs counts fnReports.2 argReports.2
  have updated := successorBranchIntro certain (unaryAfter base currentKey)
    (binaryAfter P (measureAt 2) (measureAt 3)) (out.relabel j) z xs enough computed
  have next := exact_OpenSelectedMemoSuccessor R body β Δ (out.relabel j) prior old table updated
  exact (projection R (out.relabel j) (auxiliaryTerm d c fn' arg')).mpr next

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenEvaluationProof
