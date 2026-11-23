module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinLeastRepresentativeApplicationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalPairedPackedLeastChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredAuxEdgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedLeastFromCoveredWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoThinLiftGapProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRoundApplicationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoThinLiftGapProof (pairRelabel)
open NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof (ParentWindowsAt)
open NumberedWindowInternalRankMeasuredAuxEdgeProof (exact_OpenRankMeasuredAuxEdge)
open NumberedWindowInternalRankMeasuredExchangeOpenProof (exact_OpenRankMeasuredPackedEdge)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalThinPairedLeastFromCoveredWindowProof (exact_OpenThinPairedLeastFromCoveredWindow)
open NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
open NumberedWindowInternalOriginalPairedPackedLeastChecks
open NumberedWindowInternalThinLeastRepresentativeApplicationProof
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets

private theorem arrowRename {α β : Type} (dom cod : OTerm α) (j : α → β) :
    (rawCons dom cod).relabel j = rawCons (dom.relabel j) (cod.relabel j) := by
  simp only [rawCons,sucRelabel,pairRelabel]

theorem exact_OpenRankMeasuredMotiveStep (s : Settings) (base : Program 2) (V baseM g : Program 1)
    (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg μ m : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    let E := edge4 X W
    ParentWindowsAt E W B Γ ctx dom cod arg →
    ApplicationEdgeStepAt E R C X W s B Γ ctx (rawCons dom cod) ctx cod dom cod arg μ m := by
  intro M C W R D X E windows β j Δ f g' keep edge held
  rw [arrowRename] at edge
  have typed := windows β j Δ f g' keep edge
  obtain ⟨data⟩ := held
  obtain ⟨edge⟩ := edge
  obtain ⟨law⟩ := exact_OpenRankMeasuredPackedEdge C W s R D B β Δ
    (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (μ.relabel j) f g'
  have share := Derivation.implicationElimination law
    (Derivation.conjunctionIntroduction edge (Derivation.conjunctionLeft data))
  let cj := ctx.relabel j
  let dj := dom.relabel j
  let tj := cod.relabel j
  let aj := arg.relabel j
  have parent := exact_OpenRankMeasuredAuxEdge s base V baseM g P G baseW B β Δ
    cj dj tj f g' aj (μ.relabel j) ⟨edge⟩ ⟨Derivation.conjunctionLeft data⟩ typed.1 typed.2
  obtain ⟨moved⟩ := exact_OpenThinPairedLeastFromCoveredWindow
    exact_OriginalPhysicalCountLength exact_OriginalPhysicalCountStrict C (measuredExchange R D)
    (syntaxWindow baseW V) s cj tj (auxiliaryTerm dj tj f aj) (auxiliaryTerm dj tj g' aj) (m.relabel j)
    ⟨Derivation.conjunctionRight data⟩ parent typed.2
  exact ⟨Derivation.conjunctionIntroduction share moved⟩

/-- The actual least of a function is a valid application
representative in the rank-tested exact measured original programs,
under the genuine typed parent-window law. No same-raw representative
premise or extra round, length, or selected-cover report is held. -/
theorem exact_OpenRankMeasuredRepresentative (s : Settings) (base : Program 2)
    (V baseM g : Program 1) (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f q arg μ m : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    ParentWindowsAt (edge4 X W) W B Γ ctx dom cod arg →
    Nonempty (Derivation B Γ (unary R μ f)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx (rawCons dom cod) f q)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation B Γ (appMotive R C X W s ctx cod dom cod arg μ m q)) := by
  intro M C W R D X windows hμ klass applied
  obtain ⟨hμ⟩ := hμ
  obtain ⟨applied⟩ := applied
  exact exact_ThinLeastRepresentativeApplication C X W s R C X W s B α Γ ctx (rawCons dom cod) f q
    ctx cod dom cod arg μ m
    (exact_OpenRankMeasuredMotiveStep s base V baseM g P G baseW B α Γ ctx dom cod arg μ m windows)
    ⟨Derivation.conjunctionIntroduction hμ applied⟩ klass

#print axioms exact_OpenRankMeasuredMotiveStep
#print axioms exact_OpenRankMeasuredRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRoundApplicationProof
