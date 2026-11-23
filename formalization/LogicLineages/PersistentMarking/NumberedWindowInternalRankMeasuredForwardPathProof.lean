module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredMatchedPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedForwardBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredForwardPathProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (exact_CoveredWindowReport)
open NumberedWindowInternalThinFormationRepresentativeTargets (formation)
open NumberedWindowInternalThinFormationRepresentativeSyntaxProof (atFunction formationRename)
open NumberedWindowInternalThinMatchedAdvanceCompositionProof (pullCases)
open NumberedWindowInternalRankMeasuredMatchedPathProof (exact_OriginalRankMeasuredMatchedPath)
open NumberedWindowInternalThinMatchedForwardBindingProof

/-- Forward orientation of the genuine arbitrary application path on the rank-tested exchange tuple.
The actual later function window gives a real later least, and the proved
matching theorem supplies the earlier path with the same earlier value by
functionality. No separate forward induction, opening by reflection, or
premise of a mapped path is used. -/
theorem exact_OpenOriginalRankMeasuredForwardPath (s : Settings) (base : Program 2)
    (V baseM g : Program 1) (P : Program 2) (G baseW root other : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f n cert value : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    let raw := typedRaw5 root other W V
    let L := packedLeastProgram C X W s
    Nonempty (Derivation B Γ (formation W ctx dom cod arg)) →
    Nonempty (Derivation B Γ (windowAt W ctx (rawCons dom cod) n)) →
    Nonempty (Derivation B Γ (positiveAt raw L ctx (rawCons dom cod) f cert n)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value)) →
    Nonempty (Derivation B Γ (pushed C X W s raw ctx cod (auxiliaryTerm dom cod n arg) value)) := by
  intro M C W R D X raw L held typed path earlier
  obtain ⟨form⟩ := held
  obtain ⟨fn⟩ := typed
  obtain ⟨here⟩ := atFunction W ctx dom cod arg n form
  obtain ⟨covered⟩ := exact_CoveredWindowReport C X s (syntaxWindow baseW V) B α Γ
    ctx cod (auxiliaryTerm dom cod n arg)
  have facts := Derivation.implicationElimination covered (Derivation.implicationElimination here fn)
  apply casesLeast C X W s ctx cod (auxiliaryTerm dom cod n arg) _
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight facts)⟩
  intro β j Δ later keep found
  rw [pushedRename,auxiliaryRename]
  rw [auxiliaryRename] at found
  have d := renameInto ⟨form⟩ j Δ keep
  rw [formationRename] at d
  have before := renameInto path j Δ keep
  rw [positiveRename,rawConsRename] at before
  have e := renameInto earlier j Δ keep
  rw [leastRename,auxiliaryRename] at e
  obtain ⟨rule⟩ := exact_OriginalRankMeasuredMatchedPath s base V baseM g P G baseW root other B β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (f.relabel j) (n.relabel j)
    (cert.relabel j) later
  obtain ⟨d⟩ := d
  obtain ⟨before⟩ := before
  obtain ⟨laterRun⟩ := found
  have matched := Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction d (Derivation.conjunctionIntroduction before laterRun))
  apply pullCases C X W s raw (ctx.relabel j) (cod.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (f.relabel j) (arg.relabel j)) later _ ⟨matched⟩
  intro γ k Θ q keep2 came mapped
  rw [pushedRename,auxiliaryRename]
  rw [auxiliaryRename] at came
  have e' := renameInto e k Θ keep2
  rw [leastRename,auxiliaryRename] at e'
  have final := renameInto ⟨laterRun⟩ k Θ keep2
  rw [leastRename,auxiliaryRename] at final
  obtain ⟨same⟩ := valueUnique L (suc q) (suc ((value.relabel j).relabel k))
    ![((ctx.relabel j).relabel k),((cod.relabel j).relabel k),
      auxiliaryTerm ((dom.relabel j).relabel k) ((cod.relabel j).relabel k)
        ((f.relabel j).relabel k) ((arg.relabel j).relabel k)] ⟨came⟩ e'
  obtain ⟨t⟩ := moveSource raw L ((ctx.relabel j).relabel k) ((cod.relabel j).relabel k) q
    ((value.relabel j).relabel k) (later.relabel k) (cancelSuc same) mapped
  obtain ⟨final⟩ := final
  exact provideLater C X W s raw ((ctx.relabel j).relabel k) ((cod.relabel j).relabel k)
    (auxiliaryTerm ((dom.relabel j).relabel k) ((cod.relabel j).relabel k)
      ((n.relabel j).relabel k) ((arg.relabel j).relabel k))
    ((value.relabel j).relabel k) (later.relabel k) final t

#print axioms exact_OpenOriginalRankMeasuredForwardPath
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredForwardPathProof
