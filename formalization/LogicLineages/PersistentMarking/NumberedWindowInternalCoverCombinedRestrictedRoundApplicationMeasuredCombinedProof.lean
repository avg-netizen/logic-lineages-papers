module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredCombinedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename inputsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseScalarEdge (edge4 exchangeTape)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange thinSwapExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange compareMeasurements)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof (exact_RoundApplicationLeastAt)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
  (exact_CombinedApplicationLeastStep exact_CombinedApplicationEdgeStepAt)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
  (exact_MeasuredExchangePreservesMeasure)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
  (exact_LeastRepresentativeApplication)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets

attribute [local irreducible] programGraph

theorem exact_MeasuredToPlainEdge : ExactMeasuredToPlainEdge := by
  intro C s M D W body α Γ ctx ty w k e
  let Dm := measuredExchange M D
  let Xm := guardedExchange C s (thinPairedExchange Dm)
  let X := guardedExchange C s (thinPairedExchange D)
  obtain ⟨e⟩ := e
  obtain ⟨lawM⟩ := exact_OpenPackedScalarEdge Xm W body α Γ ctx ty w k
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawM) e
  have windows := Derivation.conjunctionRight calls
  obtain ⟨g⟩ := conjunctionRecover (thinPairedExchange Dm) (compareOptions C s) (exchangeTape w k)
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pp⟩ := conjunctionRecover Dm (thinSwapExchange Dm) (exchangeTape w k) ⟨Derivation.conjunctionLeft g⟩
  obtain ⟨fwdM⟩ := conjunctionRecover D (compareMeasurements M) (exchangeTape w k) ⟨Derivation.conjunctionLeft pp⟩
  have revDm : Nonempty (Derivation body Γ (programGraph Dm (suc z) (exchangeTape k w))) := by
    apply compositionRecover Dm ![.projection 1,.projection 0] (suc z) (exchangeTape w k) ![k,w]
      ⟨Derivation.conjunctionRight pp⟩
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · exact projectionValue 1 (exchangeTape w k)
    · obtain rfl := Fin.eq_zero t
      exact projectionValue 0 (exchangeTape w k)
  obtain ⟨revM⟩ := conjunctionRecover D (compareMeasurements M) (exchangeTape k w) revDm
  have swap : Nonempty (Derivation body Γ (programGraph (thinSwapExchange D) (suc z) (exchangeTape w k))) := by
    apply compositionValue D ![.projection 1,.projection 0] (suc z) (exchangeTape w k) ![k,w]
      ⟨Derivation.conjunctionLeft revM⟩
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · exact projectionValue 1 (exchangeTape w k)
    · obtain rfl := Fin.eq_zero t
      exact projectionValue 0 (exchangeTape w k)
  have paired := conjunctionAccept D (thinSwapExchange D) (exchangeTape w k)
    ⟨Derivation.conjunctionLeft fwdM⟩ swap
  obtain ⟨guarded⟩ := conjunctionAccept (thinPairedExchange D) (compareOptions C s) (exchangeTape w k)
    paired ⟨Derivation.conjunctionRight g⟩
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx ty w k
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight lawX)
    (Derivation.conjunctionIntroduction guarded windows)⟩

theorem exact_MeasuredCombinedApplicationEdgeStepAt : ExactMeasuredCombinedApplicationEdgeStepAt := by
  intro V TV M M0 B T base s body α Γ ctx dom cod arg μ m P W D X Xm syn ty argument
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
  have mwl : Derivation body Δ (leastGraph P.cover X W s (ctx.relabel j) (cod.relabel j)
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) w (arg.relabel j)) (m.relabel j)) :=
    Derivation.conjunctionRight mwd
  have plain := exact_MeasuredToPlainEdge P.cover s (selectedMeasure P.R) D W body β Δ (ctx.relabel j)
    (rawCons (dom.relabel j) (cod.relabel j)) w k e
  obtain ⟨ed⟩ := e
  obtain ⟨pres⟩ := exact_MeasuredExchangePreservesMeasure P.cover s (selectedMeasure P.R) D W body β Δ
    (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (μ.relabel j) w k
  have mk := Derivation.implicationElimination pres (Derivation.conjunctionIntroduction ed mwm)
  obtain ⟨lk⟩ := exact_CombinedApplicationLeastStep V TV M M0 B T base s body β Δ (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) w k syn' ty' argument'
    plain ⟨mwm⟩ ⟨mk⟩ ⟨mwl⟩
  exact ⟨Derivation.conjunctionIntroduction mk lk⟩

theorem exact_MeasuredCombinedRoundApplicationLeast : ExactMeasuredCombinedRoundApplicationLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f arg μ m i vertices out k P W D X Xm syn ty argument
    mf lf round member
  have step := exact_MeasuredCombinedApplicationEdgeStepAt V TV M M0 B T base s body α Γ ctx dom cod arg μ m
    syn ty argument
  obtain ⟨mf⟩ := mf
  obtain ⟨lf⟩ := lf
  exact exact_RoundApplicationLeastAt (edge4 Xm W) (selectedMeasure P.R) P.cover X W s body α Γ
    i vertices ctx (rawCons dom cod) f out k ctx cod dom cod arg μ m step
    ⟨Derivation.conjunctionIntroduction mf lf⟩ round member

theorem exact_CombinedLeastRepresentativeApplication : ExactCombinedLeastRepresentativeApplication := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f x arg m P W X meas syn ty argument lf lx
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
  have step := exact_CombinedApplicationEdgeStepAt V TV M M0 B T base s body β Δ (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) meas syn' ty' argument'
  obtain ⟨mf⟩ := mf
  obtain ⟨lf'⟩ := lf'
  obtain ⟨d⟩ := exact_LeastRepresentativeApplication P.cover X W s (selectedMeasure P.R) P.cover X W s
    body β Δ (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (f.relabel j) (x.relabel j)
    (ctx.relabel j) (cod.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) step
    ⟨Derivation.conjunctionIntroduction mf lf'⟩ lx'
  exact ⟨Derivation.conjunctionRight d⟩

theorem exact_MeasuredCombinedLeastRepresentativeApplication :
    ExactMeasuredCombinedLeastRepresentativeApplication := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f x arg m P W D X Xm syn ty argument lf lx
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
  have step := exact_MeasuredCombinedApplicationEdgeStepAt V TV M M0 B T base s body β Δ (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) syn' ty' argument'
  obtain ⟨mf⟩ := mf
  obtain ⟨lf'⟩ := lf'
  obtain ⟨d⟩ := exact_LeastRepresentativeApplication P.cover Xm W s (selectedMeasure P.R) P.cover X W s
    body β Δ (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (f.relabel j) (x.relabel j)
    (ctx.relabel j) (cod.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) μ (m.relabel j) step
    ⟨Derivation.conjunctionIntroduction mf lf'⟩ lx'
  exact ⟨Derivation.conjunctionRight d⟩

#print axioms exact_MeasuredToPlainEdge
#print axioms exact_MeasuredCombinedApplicationEdgeStepAt
#print axioms exact_MeasuredCombinedRoundApplicationLeast
#print axioms exact_CombinedLeastRepresentativeApplication
#print axioms exact_MeasuredCombinedLeastRepresentativeApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredCombinedProof
