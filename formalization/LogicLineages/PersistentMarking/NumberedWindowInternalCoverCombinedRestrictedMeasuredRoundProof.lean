module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename inputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseScalarEdge (edge4 edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof (exact_RoundApplicationLeastAt)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
  (exact_MeasuredExchangePreservesMeasure)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
  (exact_LeastRepresentativeApplication)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastProof
  (exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets
open NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets

attribute [local irreducible] programGraph

/-- The edge step over the one measured exchange: the member's measure moves
along the measured edge (`exact_MeasuredExchangePreservesMeasure`), and the
held application least moves because the measured paired common least gives
one `x` that is the least at both applications, and the least program is
functional, so `x` is the held `m`. -/
theorem exact_FullyMeasuredApplicationEdgeStepAt : ExactFullyMeasuredApplicationEdgeStepAt := by
  intro V TV M M0 B T base s body α Γ ctx dom cod arg μ m P W D Xm syn ty argument
  intro β j Δ w k keep e mw
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  rw [rawConsRename] at e
  obtain ⟨mwd⟩ := mw
  have mwm : Derivation body Δ (unary (selectedMeasure P.R) (μ.relabel j) w) :=
    Derivation.conjunctionLeft mwd
  have mwl : Derivation body Δ (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j)
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) w (arg.relabel j)) (m.relabel j)) :=
    Derivation.conjunctionRight mwd
  obtain ⟨ed⟩ := e
  obtain ⟨pres⟩ := exact_MeasuredExchangePreservesMeasure P.cover s (selectedMeasure P.R) D W body β Δ
    (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (μ.relabel j) w k
  have mk := Derivation.implicationElimination pres (Derivation.conjunctionIntroduction ed mwm)
  have edge : Nonempty (Derivation body Δ
      (edgeGraph Xm W (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) w k)) := ⟨ed⟩
  have lk : Nonempty (Derivation body Δ (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j)
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) k (arg.relabel j)) (m.relabel j))) := by
    apply exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast V TV M M0 B T base s body β Δ
      (ctx.relabel j) (dom.relabel j) (cod.relabel j) w k (arg.relabel j)
      (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) k (arg.relabel j)) (m.relabel j))
      syn' ty' argument' edge
    intro γ i Θ x retain la lb
    rw [leastRename]
    have lm := renameInto ⟨mwl⟩ i Θ retain
    rw [leastRename] at lm
    have same := valueUnique (packedLeastProgram P.cover Xm W s) (suc x) (suc ((m.relabel j).relabel i))
      ![(ctx.relabel j).relabel i,(cod.relabel j).relabel i,
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) w (arg.relabel j)).relabel i] la lm
    exact outputTransport (packedLeastProgram P.cover Xm W s) (suc x) (suc ((m.relabel j).relabel i))
      ![(ctx.relabel j).relabel i,(cod.relabel j).relabel i,
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) k (arg.relabel j)).relabel i] same lb
  obtain ⟨lk⟩ := lk
  exact ⟨Derivation.conjunctionIntroduction mk lk⟩

theorem exact_FullyMeasuredRoundApplicationLeast : ExactFullyMeasuredRoundApplicationLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f arg μ m i vertices out k P W D Xm syn ty argument
    mf lf round member
  have step := exact_FullyMeasuredApplicationEdgeStepAt V TV M M0 B T base s body α Γ ctx dom cod arg μ m
    syn ty argument
  obtain ⟨mf⟩ := mf
  obtain ⟨lf⟩ := lf
  exact exact_RoundApplicationLeastAt (edge4 Xm W) (selectedMeasure P.R) P.cover Xm W s body α Γ
    i vertices ctx (rawCons dom cod) f out k ctx cod dom cod arg μ m step
    ⟨Derivation.conjunctionIntroduction mf lf⟩ round member

theorem exact_FullyMeasuredLeastRepresentativeApplication :
    ExactFullyMeasuredLeastRepresentativeApplication := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f x arg m P W D Xm syn ty argument lf lx
  apply programCases (selectedMeasure P.R) ![f] _
  intro β j Δ μ keep mf
  rw [inputsRename] at mf
  rw [leastRename,appAuxRename]
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  have lf' := renameInto lf j Δ keep
  rw [leastRename,appAuxRename] at lf'
  have lx' := renameInto lx j Δ keep
  rw [leastRename,rawConsRename] at lx'
  have step := exact_FullyMeasuredApplicationEdgeStepAt V TV M M0 B T base s body β Δ (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) syn' ty' argument'
  obtain ⟨mf⟩ := mf
  obtain ⟨lf'⟩ := lf'
  obtain ⟨d⟩ := exact_LeastRepresentativeApplication P.cover Xm W s (selectedMeasure P.R) P.cover Xm W s
    body β Δ (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (f.relabel j) (x.relabel j)
    (ctx.relabel j) (cod.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) step
    ⟨Derivation.conjunctionIntroduction mf lf'⟩ lx'
  exact ⟨Derivation.conjunctionRight d⟩

#print axioms exact_FullyMeasuredApplicationEdgeStepAt
#print axioms exact_FullyMeasuredRoundApplicationLeast
#print axioms exact_FullyMeasuredLeastRepresentativeApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
