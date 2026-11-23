module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredCombinedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareShared)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange thinSwapExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (compareOptions)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
  (exact_MeasuredExchangePreservesMeasure)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredCombinedProof
  (exact_MeasuredToPlainEdge)
open NumberedWindowInternalCombinedMeasuredRouteTargets

attribute [local irreducible] programGraph

theorem exact_InstalledMeasuredEdge : ExactInstalledMeasuredEdge := by
  intro s V TV M M0 B T base K
  refine ⟨exact_MeasuredExchangePreservesMeasure K.cover s K.measure K.directed K.window,?_⟩
  intro body α Γ ctx ty a b held
  exact exact_MeasuredToPlainEdge K.cover s K.measure K.directed K.window body α Γ ctx ty a b held

theorem exact_InstalledAdmissionFromSharedMeasure : ExactInstalledAdmissionFromSharedMeasure := by
  intro s V TV M M0 B T base body α Γ ctx ty a b p K plain ma mb
  let D := K.directed
  let N := K.measure
  let Dm := measuredExchange N D
  let cover := compareOptions K.cover s
  obtain ⟨plain⟩ := plain
  obtain ⟨lawP⟩ := exact_OpenPackedScalarEdge K.plain K.window body α Γ ctx ty a b
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawP) plain
  obtain ⟨guard⟩ := conjunctionRecover (thinPairedExchange D) cover (exchangeTape a b)
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pair⟩ := conjunctionRecover D (thinSwapExchange D) (exchangeTape a b)
    ⟨Derivation.conjunctionLeft guard⟩
  have rev : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape b a))) := by
    apply compositionRecover D ![.projection 1,.projection 0] (suc z) (exchangeTape a b) ![b,a]
      ⟨Derivation.conjunctionRight pair⟩
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · exact projectionValue 1 (exchangeTape a b)
    · obtain rfl := Fin.eq_zero t
      exact projectionValue 0 (exchangeTape a b)
  have fwdM := conjunctionAccept D (compareMeasurements N) (exchangeTape a b)
    ⟨Derivation.conjunctionLeft pair⟩ (compareShared N a b p ma mb)
  have revM := conjunctionAccept D (compareMeasurements N) (exchangeTape b a) rev
    (compareShared N b a p mb ma)
  have swapM : Nonempty (Derivation body Γ (programGraph (thinSwapExchange Dm) (suc z) (exchangeTape a b))) := by
    apply compositionValue Dm ![.projection 1,.projection 0] (suc z) (exchangeTape a b) ![b,a] revM
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · exact projectionValue 1 (exchangeTape a b)
    · obtain rfl := Fin.eq_zero t
      exact projectionValue 0 (exchangeTape a b)
  have paired := conjunctionAccept Dm (thinSwapExchange Dm) (exchangeTape a b) fwdM swapM
  obtain ⟨guarded⟩ := conjunctionAccept (thinPairedExchange Dm) cover (exchangeTape a b)
    paired ⟨Derivation.conjunctionRight guard⟩
  obtain ⟨lawM⟩ := exact_OpenPackedScalarEdge K.exchange K.window body α Γ ctx ty a b
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight lawM)
    (Derivation.conjunctionIntroduction guarded (Derivation.conjunctionRight calls))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteProof
