module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel orderRename)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename liftTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody boundReport)
open NumberedWindowInternalChosenAuxMeasureObservedTargets (parentMeasureAndBounds)

attribute [local irreducible] programGraph
variable {α β : Type}

theorem priorRename (dom cod fn arg : OTerm α) (j : α → β) :
    (memoPrior dom cod fn arg).relabel j =
      memoPrior (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  have pairRename (a b : OTerm α) :
      (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [memoPrior,pairRename,rawConsRename,numeralRename,zRelabel]

theorem measureRename (base : Program 1) (out key : OTerm α) (j : α → β) :
    (measureGraph base chosenCombine out key).relabel j =
      measureGraph base chosenCombine (out.relabel j) (key.relabel j) :=
  unaryRename (selectedMeasure (measureUpdate base chosenCombine)) out key j

theorem pairRename (m d b : OTerm α) (j : α → β) :
    (codePair m d b).relabel j = codePair (m.relabel j) (d.relabel j) (b.relabel j) := by
  simp only [codePair,programRename,binaryInputsRename]

theorem parentReportRename (base : Program 1) (dom cod fn arg p df da bf ba : OTerm α)
    (j : α → β) :
    (parentMeasureAndBounds base dom cod fn arg p df da bf ba).relabel j =
      parentMeasureAndBounds base (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
        (p.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) := by
  simp only [parentMeasureAndBounds,conjunctionRename,measureRename,auxiliaryRename,
    existsRename,boundBody,boundReport,pairRename,sucRelabel,addRelabel,orderRename,liftTermRename,Term.relabel]
  <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
