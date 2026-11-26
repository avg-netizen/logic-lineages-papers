module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoLookupProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxMeasureStepTargets (measureAt)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalCoverSharedMemoTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverSharedMemoEarlierValue : ExactOpenCoverSharedMemoEarlierValue := by
  intro R slot body α Γ child prior old out key fieldReport small table hit
  apply programCases (scratchRow (constantZero 2) R) ![child,z,z] _
  intro β j Δ value keep actual
  simp only [unaryRename]
  simp only [tripleInputsRename,zRelabel] at actual
  have key' := renameInto key j Δ keep
  have field' := renameInto fieldReport j Δ keep
  have small' := renameInto small j Δ keep
  have table' := renameInto table j Δ keep
  have hit' := renameInto hit j Δ keep
  simp only [programRename,quadInputsRename,zRelabel,sucRelabel] at key' field' hit'
  simp only [orderRename,sucRelabel] at small'
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at table'
  let ch := child.relabel j
  let p := prior.relabel j
  let o := old.relabel j
  have reads := slotReports R slot ch value p o key' field' small' actual table'
  let x := out.relabel j
  have same := valueUnique (measureAt slot) value x ![p,o,z,z] reads.2 hit'
  have accepted : Nonempty (Derivation body Δ (readRow R x ch)) :=
    outputTransport (scratchRow (constantZero 2) R) value x ![ch,z,z] same actual
  exact (projection R x ch).mpr accepted

#print axioms exact_OpenCoverSharedMemoEarlierValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoLookupProof
