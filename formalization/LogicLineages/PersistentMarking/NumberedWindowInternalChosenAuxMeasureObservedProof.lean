module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoThinChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureMemoThinChecks (exact_OpenChosenAuxMeasureMemoRow)
open NumberedWindowInternalChosenAuxMeasureObservedTargets
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof

attribute [local irreducible] programGraph

theorem exact_OpenChosenAuxMeasureObserved : ExactOpenChosenAuxMeasureObserved := by
  intro base body α Γ dom cod fn arg mf ma df da bf ba p hf ha pf pa emit
  let R := measureUpdate base chosenCombine
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,z,z] _
  intro β j Δ old keep table
  rw [parentReportRename]
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  have hf' := renameInto hf j Δ keep
  have ha' := renameInto ha j Δ keep
  have pf' := renameInto pf j Δ keep
  have pa' := renameInto pa j Δ keep
  have emit' := renameInto emit j Δ keep
  rw [measureRename] at hf' ha'
  rw [pairRename] at pf' pa'
  rw [programRename,binaryInputsRename] at emit'
  obtain ⟨row⟩ := exact_OpenChosenAuxMeasureMemoRow base body β Δ
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) (mf.relabel j) (ma.relabel j)
    (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) (p.relabel j) old table hf' ha' pf' pa' emit'
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight row))⟩

#print axioms exact_OpenChosenAuxMeasureObserved

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedProof
