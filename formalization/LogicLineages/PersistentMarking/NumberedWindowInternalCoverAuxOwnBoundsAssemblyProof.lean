module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel orderRename)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename liftTermRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody boundReport)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (AuxParentInputs selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof
  (exact_OpenSelectedGrammarAuxScratchMembership)
open NumberedWindowInternalCoverSharedOwnScratchTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem boundsRename {β : Type} (p df da bf ba : OTerm α) (j : α → β) :
    (existsOne (boundBody p df da bf ba)).relabel j =
      existsOne (boundBody (p.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j)) := by
  simp only [existsRename,boundBody,boundReport,conjunctionRename,pairRename,sucRelabel,addRelabel,
    orderRename,liftTermRename,Term.relabel]
  <;> rfl

theorem fromActualBounds (V Measure : Program 1) (s : Settings)
    (p df bf da ba fState fTerms fArgs aState aTerms aArgs vertices dom cod fn arg : OTerm α)
    (f : OwnOccurrence s body Γ df bf fState fTerms fArgs fn)
    (a : OwnOccurrence s body Γ da ba aState aTerms aArgs arg)
    (bounded : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba))))
    (hd : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)))
    (hc : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg))))
    (measured : Nonempty (Derivation body Γ (unary Measure p (auxiliaryTerm dom cod fn arg))))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  obtain ⟨bounds⟩ := bounded
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
  have fg := renameInto f.observedScope j Δ keep
  have ag := renameInto a.observedScope j Δ keep
  have fh := renameInto f.ownKey j Δ keep
  have ah := renameInto a.ownKey j Δ keep
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have valid' := renameInto valid j Δ keep
  have held' := renameInto held j Δ keep
  have measured' := renameInto measured j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at fg ag
  simp only [graphRename,typesTerm,numeralRename] at hd' hc'
  rw [graphRename] at fh ah
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at valid'
  simp only [unaryRename,auxiliaryRename] at held'
  simp only [unaryRename,auxiliaryRename] at measured'
  let d := add (df.relabel j) (da.relabel j)
  have paid : AuxParentInputs V Measure s body Δ (p.relabel j) d b
      (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
      (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
      (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
      (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) :=
    { functionReport := fg, argumentReport := ag, functionMember := fh, argumentMember := ah
      functionDepth := ⟨Derivation.conjunctionLeft depths⟩
      functionWidth := ⟨Derivation.conjunctionLeft widths⟩
      argumentDepth := ⟨Derivation.conjunctionRight depths⟩
      argumentWidth := ⟨Derivation.conjunctionRight widths⟩
      domainMember := hd', codomainMember := hc', validity := valid', measure := measured'
      measureCode := ⟨Derivation.conjunctionLeft row⟩ }
  have found := exact_OpenSelectedGrammarAuxScratchMembership V Measure s body
    (α ⊕ Fin 1) Δ (p.relabel j) d b
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j)
    (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
    (vertices.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) paid held'
  rw [← auxiliaryRename,← graphRename] at found
  obtain ⟨found⟩ := found
  exact ⟨Derivation.existentialElimination bounds found⟩

#print axioms fromActualBounds
#print axioms boundsRename

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
