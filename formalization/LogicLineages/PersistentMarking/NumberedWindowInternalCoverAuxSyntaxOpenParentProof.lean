module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalCoverAuxSyntaxOpenRowProof (exact_OpenCoverAuxSyntaxRow)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverAuxSyntaxTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem childrenRename (V T : Program 1)
    (dom cod fn arg : OTerm α) {β : Type} (j : α → β) :
    (auxSyntaxChildren V T dom cod fn arg).relabel j =
      auxSyntaxChildren V T (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) := by
  simp only [auxSyntaxChildren,conjunctionRename,unaryRename,sucRelabel,zRelabel]

private theorem atUpdate (V T : Program 1)
    (dom cod fn arg old value : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (unary (auxSyntax V T) (suc z) (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (tableAt (auxSyntaxUpdate V T) old (memoPrior dom cod fn arg))))
    (update : Nonempty (Derivation body Γ
      (programGraph (auxSyntaxUpdate V T) value (auxTape dom cod fn arg old)))) :
    Nonempty (Derivation body Γ (auxSyntaxChildren V T dom cod fn arg)) := by
  let R := auxSyntaxUpdate V T
  let key := auxiliaryTerm dom cod fn arg
  let prior := memoPrior dom cod fn arg
  have parentRow := (projection R (suc z) key).mp parent
  have actual := exact_OpenSelectedMemoSuccessor R body α Γ value prior old table update
  have agree := valueUnique (scratchRow (constantZero 2) R) value (suc z) ![key,z,z] actual parentRow
  have atSameOutput := outputTransport R value (suc z) ![prior,old,z,z] agree update
  exact exact_OpenCoverAuxSyntaxRow V T body α Γ dom cod fn arg old table atSameOutput

private theorem withTable (V T : Program 1)
    (dom cod fn arg old : OTerm α)
    (parent : Nonempty (Derivation body Γ
      (unary (auxSyntax V T) (suc z) (auxiliaryTerm dom cod fn arg))))
    (table : Nonempty (Derivation body Γ
      (tableAt (auxSyntaxUpdate V T) old (memoPrior dom cod fn arg)))) :
    Nonempty (Derivation body Γ (auxSyntaxChildren V T dom cod fn arg)) := by
  let R := auxSyntaxUpdate V T
  apply programCases R ![memoPrior dom cod fn arg,old,z,z] _
  intro β j Δ value keep update
  simp only [quadInputsRename,priorRename,zRelabel] at update
  rw [childrenRename]
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  simp only [tableAt,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  exact atUpdate V T (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) (old.relabel j) value parent' table' update

theorem exact_OpenCoverAuxSyntaxParent : ExactOpenCoverAuxSyntaxParent := by
  intro V T body α Γ dom cod fn arg parent
  let R := auxSyntaxUpdate V T
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,z,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  rw [childrenRename]
  have parent' := renameInto parent j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at parent'
  exact withTable V T (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) old parent' table

#print axioms exact_OpenCoverAuxSyntaxParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
