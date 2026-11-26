module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureObservedTargets (parentMeasureAndBounds)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename pairRename parentReportRename)
open NumberedWindowInternalChosenAuxMeasureObservedProof (exact_OpenChosenAuxMeasureObserved)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureParentTargets

attribute [local irreducible] programGraph

/-- Carry the two reports for a child together through an object witness binder. -/
theorem moveChild {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} (M : Program 1)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {q m d b : OTerm α} (child : AuxMeasureChild M body Γ q m d b) :
    AuxMeasureChild M body Δ (q.relabel j) (m.relabel j) (d.relabel j) (b.relabel j) := by
  have observed := renameInto child.observed j Δ keep
  have coords := renameInto child.coords j Δ keep
  rw [measureRename] at observed
  rw [pairRename] at coords
  exact ⟨observed,coords⟩

theorem exact_OpenChosenAuxMeasureAlign : ExactOpenChosenAuxMeasureAlign := by
  intro M body α Γ dom cod fn arg mf ma p df da bf ba parent fnData argData
  let P := selectedMeasure (measureUpdate M chosenCombine)
  have both : Nonempty (Derivation body Γ
      (programGraph chosenCombine p ![mf,ma] ⊓ parentMeasureAndBounds M dom cod fn arg p df da bf ba)) := by
    apply programCases chosenCombine ![mf,ma] _
    intro β j Δ value keep actual
    simp only [binaryInputsRename] at actual
    simp only [conjunctionRename,programRename,binaryInputsRename,parentReportRename]
    let dom' := dom.relabel j
    let cod' := cod.relabel j
    let fn' := fn.relabel j
    let arg' := arg.relabel j
    let mf' := mf.relabel j
    let ma' := ma.relabel j
    let p' := p.relabel j
    let df' := df.relabel j
    let da' := da.relabel j
    let bf' := bf.relabel j
    let ba' := ba.relabel j
    let key := auxiliaryTerm dom' cod' fn' arg'
    have parent' := renameInto parent j Δ keep
    rw [measureRename,auxiliaryRename] at parent'
    have f := moveChild M j Δ keep fnData
    have a := moveChild M j Δ keep argData
    obtain ⟨guess⟩ := exact_OpenChosenAuxMeasureObserved M body β Δ dom' cod' fn' arg'
      mf' ma' df' da' bf' ba' value f.observed a.observed f.coords a.coords actual
    have agrees := valueUnique P value p' ![key] ⟨Derivation.conjunctionLeft guess⟩ parent'
    have sameOutput := outputTransport chosenCombine value p' ![mf',ma'] agrees actual
    obtain ⟨bounds⟩ := exact_OpenChosenAuxMeasureObserved M body β Δ dom' cod' fn' arg'
      mf' ma' df' da' bf' ba' p' f.observed a.observed f.coords a.coords sameOutput
    obtain ⟨combine⟩ := sameOutput
    exact ⟨Derivation.conjunctionIntroduction combine bounds⟩
  obtain ⟨compiled⟩ := both
  exact ⟨⟨Derivation.conjunctionLeft compiled⟩,⟨Derivation.conjunctionRight compiled⟩⟩

#print axioms exact_OpenChosenAuxMeasureAlign

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
