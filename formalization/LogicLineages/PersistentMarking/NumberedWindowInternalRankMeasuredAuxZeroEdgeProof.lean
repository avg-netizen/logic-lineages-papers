module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredPackedEdgeComparisonProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenZeroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredAuxZeroEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
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

/-- A zero-rank function exchange really lifts to a rank-tested
auxiliary exchange under the two original typed parent windows.
Only the source function's rank-zero report is held. The existing
child edge gives the destination report and the two real transparent
parent rank programs compute their zero outputs. -/
theorem exact_OpenRankMeasuredAuxZeroEdge (s : Settings) (base : Program 2)
    (V baseM g : Program 1) (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f q arg : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s (auxRank g) D
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod q arg
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx (rawCons dom cod) f q)) →
    Nonempty (Derivation B Γ (unary (auxRank g) z f)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod a)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod b)) →
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx cod a b)) := by
  intro M C W D X a b ranked first wa wb
  obtain ⟨keep⟩ := exact_OpenRankMeasuredPackedEdge C W s (auxRank g) D B α Γ ctx (rawCons dom cod) z f q
  obtain ⟨edge⟩ := ranked
  obtain ⟨zero⟩ := first
  have second := Derivation.implicationElimination keep (Derivation.conjunctionIntroduction edge zero)
  have za := exact_OpenTransparentAuxRankZeroIntro g B α Γ dom cod f arg ⟨zero⟩
  have zb := exact_OpenTransparentAuxRankZeroIntro g B α Γ dom cod q arg ⟨second⟩
  obtain ⟨ordinary⟩ := exact_OpenForgetRankMeasuredPackedEdge C W s (auxRank g) D ctx (rawCons dom cod) f q ⟨edge⟩
  obtain ⟨lift⟩ := exact_UnrestrictedMeasuredFunctionEdge s base V baseM P G baseW B α Γ ctx dom cod f q arg
  obtain ⟨wa⟩ := wa
  obtain ⟨wb⟩ := wb
  have parent := Derivation.implicationElimination lift
    (Derivation.conjunctionIntroduction ordinary (Derivation.conjunctionIntroduction wa wb))
  exact exact_OpenInsertRankMeasuredPackedEdge C W s (auxRank g) D ctx cod a b z ⟨parent⟩ za zb

#print axioms exact_OpenRankMeasuredAuxZeroEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredAuxZeroEdgeProof
