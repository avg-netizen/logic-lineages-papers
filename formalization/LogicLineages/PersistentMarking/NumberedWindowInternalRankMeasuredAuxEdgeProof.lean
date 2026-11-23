module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredPackedEdgeComparisonProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenZeroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredAuxEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (outputTransport programRename zeroSuccessorCases)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalRankMeasuredExchangeOpenProof (exact_OpenRankMeasuredPackedEdge)
open NumberedWindowInternalRankMeasuredPackedEdgeComparisonProof
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalTransparentAuxRankOpenZeroProof (exact_OpenTransparentAuxRankZeroIntro)
open NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof (exact_UnrestrictedMeasuredFunctionEdge)

open NumberedWindowInternalTransparentAuxRankOpenSuccessorProof (exact_OpenTransparentAuxRankSuccessorIntro)

private theorem edgeRename {α β : Type} (E : Program 4) (ctx ty a b : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty a b).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

/-- The literal extra rank gate survives auxiliary application at every
actual source rank. Its value on the other function is derived from the
held rank-tested child edge, and the common value at the two parents is
computed by the two physical tag-six rank branches. The original parent
typing windows are the only extra edge-formation premises. -/
theorem exact_OpenRankMeasuredAuxEdge (s : Settings) (base : Program 2)
    (V baseM g : Program 1) (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f q arg r : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s (auxRank g) D
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod q arg
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx (rawCons dom cod) f q)) →
    Nonempty (Derivation B Γ (unary (auxRank g) r f)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod a)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod b)) →
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx cod a b)) := by
  intro M C W D X a b ranked first wa wb
  obtain ⟨keep⟩ := exact_OpenRankMeasuredPackedEdge C W s (auxRank g) D B α Γ ctx (rawCons dom cod) r f q
  obtain ⟨edge⟩ := ranked
  obtain ⟨rankF⟩ := first
  have second := Derivation.implicationElimination keep (Derivation.conjunctionIntroduction edge rankF)
  obtain ⟨ordinary⟩ := exact_OpenForgetRankMeasuredPackedEdge C W s (auxRank g) D ctx (rawCons dom cod) f q ⟨edge⟩
  obtain ⟨lift⟩ := exact_UnrestrictedMeasuredFunctionEdge s base V baseM P G baseW B α Γ ctx dom cod f q arg
  obtain ⟨wa⟩ := wa
  obtain ⟨wb⟩ := wb
  have parent := Derivation.implicationElimination lift
    (Derivation.conjunctionIntroduction ordinary (Derivation.conjunctionIntroduction wa wb))
  apply zeroSuccessorCases Γ r (acceptEdge (edge4 X W) ctx cod a b)
  · let E := eqn r z
    let Δ := E :: Γ
    have same : Nonempty (Derivation B Δ E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have first0 := outputTransport (auxRank g) r z ![f] same (withHyp ⟨rankF⟩ E)
    have second0 := outputTransport (auxRank g) r z ![q] same (withHyp ⟨second⟩ E)
    have za := exact_OpenTransparentAuxRankZeroIntro g B α Δ dom cod f arg first0
    have zb := exact_OpenTransparentAuxRankZeroIntro g B α Δ dom cod q arg second0
    exact exact_OpenInsertRankMeasuredPackedEdge C W s (auxRank g) D ctx cod a b z (withHyp ⟨parent⟩ E) za zb
  · intro β j Δ t mem same
    have first' := renameInto ⟨rankF⟩ j Δ mem
    have second' := renameInto ⟨second⟩ j Δ mem
    have parent' := renameInto ⟨parent⟩ j Δ mem
    rw [unaryRename] at first' second'
    rw [edgeRename] at parent' ⊢
    simp only [a,b,auxiliaryRename] at parent' ⊢
    have firstS := outputTransport (auxRank g) (r.relabel j) (suc t) ![f.relabel j] same first'
    have secondS := outputTransport (auxRank g) (r.relabel j) (suc t) ![q.relabel j] same second'
    have sa := exact_OpenTransparentAuxRankSuccessorIntro g B β Δ (dom.relabel j) (cod.relabel j)
      (f.relabel j) (arg.relabel j) t firstS
    have sb := exact_OpenTransparentAuxRankSuccessorIntro g B β Δ (dom.relabel j) (cod.relabel j)
      (q.relabel j) (arg.relabel j) t secondS
    exact exact_OpenInsertRankMeasuredPackedEdge C W s (auxRank g) D (ctx.relabel j) (cod.relabel j)
      _ _ (suc (suc t)) parent' sa sb

#print axioms exact_OpenRankMeasuredAuxEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredAuxEdgeProof
