module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody boundReport)
open NumberedWindowInternalChosenAuxMeasureObservedProof (exact_OpenChosenAuxMeasureObserved)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (AuxParentInputs)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
  (exact_OpenSelectedGrammarAuxScratchMembership)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets

attribute [local irreducible] programGraph

theorem exact_OpenSelectedGrammarAuxScratchMeasured : ExactOpenSelectedGrammarAuxScratchMeasured := by
  intro V base s body α Γ p mf ma df bf da ba fState fTerms fArgs aState aTerms aArgs
    vertices dom cod fn arg f a emit hd hc valid held
  obtain ⟨parent⟩ := exact_OpenChosenAuxMeasureObserved base body α Γ dom cod fn arg mf ma
    df da bf ba p f.measurement a.measurement f.code a.code emit
  have bounds := Derivation.conjunctionRight parent
  let j : α → α ⊕ Fin 1 := Sum.inl
  let A := boundBody p df da bf ba
  let Δ := A :: Γ.map weaken
  let b : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have row : Derivation body Δ
    (boundReport (p.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) b) :=
    Derivation.hypothesis List.mem_cons_self
  have offsets := Derivation.conjunctionRight row
  have depths := Derivation.conjunctionLeft offsets
  have widths := Derivation.conjunctionRight offsets
  have fg := renameInto f.grammar j Δ keep
  have ag := renameInto a.grammar j Δ keep
  have fh := renameInto f.occurs j Δ keep
  have ah := renameInto a.occurs j Δ keep
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have valid' := renameInto valid j Δ keep
  have held' := renameInto held j Δ keep
  have measured := renameInto (Nonempty.intro (Derivation.conjunctionLeft parent)) j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at fg ag
  simp only [graphRename,typesTerm,numeralRename] at hd' hc'
  rw [graphRename] at fh ah
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at valid'
  simp only [unaryRename,auxiliaryRename] at held'
  simp only [measureRename,auxiliaryRename] at measured
  let d := add (df.relabel j) (da.relabel j)
  have paid : AuxParentInputs V (chosenMeasure base) s body Δ (p.relabel j) d b
      (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
      (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
      (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
      (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) :=
    { functionReport := fg, argumentReport := ag, functionMember := fh, argumentMember := ah
      functionDepth := ⟨Derivation.conjunctionLeft depths⟩
      functionWidth := ⟨Derivation.conjunctionLeft widths⟩
      argumentDepth := ⟨Derivation.conjunctionRight depths⟩
      argumentWidth := ⟨Derivation.conjunctionRight widths⟩
      domainMember := hd', codomainMember := hc', validity := valid', measure := measured
      measureCode := ⟨Derivation.conjunctionLeft row⟩ }
  have found := exact_OpenSelectedGrammarAuxScratchMembership V (chosenMeasure base) s body
    (α ⊕ Fin 1) Δ (p.relabel j) d b
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    (vertices.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) paid held'
  rw [← auxiliaryRename,← graphRename] at found
  obtain ⟨found⟩ := found
  exact ⟨Derivation.existentialElimination bounds found⟩

#print axioms exact_OpenSelectedGrammarAuxScratchMeasured

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredProof
