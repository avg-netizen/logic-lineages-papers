module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationEdgeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoveredInstallationTargets
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)

theorem edgeValues : ExactCoveredEdgeValues := by
  intro C s baseX baseW body α Γ ctx ty a b x
  let X := guardedExchange C s (pairedExchange baseX)
  let W := coveredWindow C s baseW
  let P := leastGraph C X W s ctx ty a x
  let Q := leastGraph C X W s ctx ty b x
  let E := acceptEdge (edge4 X W) ctx ty a b
  let Δ := E :: Γ
  have hit : Derivation body Δ E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨openEdge⟩ := NumberedWindowInternalSparseScalarEdgeOpenChecks.exact_OpenPackedScalarEdge X W body α Δ ctx ty a b
  let calls := Derivation.implicationElimination (Derivation.conjunctionLeft openEdge) hit
  let windows := Derivation.conjunctionRight calls
  obtain ⟨src⟩ := NumberedWindowInternalSparseCoveredWindowChecks.exact_CoveredWindowReport
    C X s baseW body α Δ ctx ty a
  obtain ⟨dst⟩ := NumberedWindowInternalSparseCoveredWindowChecks.exact_CoveredWindowReport
    C X s baseW body α Δ ctx ty b
  let left := Derivation.conjunctionRight (Derivation.implicationElimination src (Derivation.conjunctionLeft windows))
  let right := Derivation.conjunctionRight (Derivation.implicationElimination dst (Derivation.conjunctionRight windows))
  obtain ⟨reverse⟩ := NumberedWindowInternalSparseSymmetricExchangeChecks.exact_PairedEdgeReversal
    C s baseX W body α Δ ctx ty a b
  let back := Derivation.implicationElimination reverse hit
  obtain ⟨fwd⟩ := NumberedWindowInternalSparseExchangeTransportChecks.exact_PairedEdgeTransport
    C s baseX W body α (P :: Δ) ctx ty a b x
  obtain ⟨rev⟩ := NumberedWindowInternalSparseExchangeTransportChecks.exact_PairedEdgeTransport
    C s baseX W body α (Q :: Δ) ctx ty b a x
  have forward : Derivation body Δ (P.imp Q) := Derivation.implicationIntroduction
    (Derivation.implicationElimination fwd (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self)
      (Derivation.conjunctionIntroduction (addHyp hit P) (addHyp (Derivation.conjunctionLeft right) P))))
  have backward : Derivation body Δ (Q.imp P) := Derivation.implicationIntroduction
    (Derivation.implicationElimination rev (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self)
      (Derivation.conjunctionIntroduction (addHyp back Q) (addHyp (Derivation.conjunctionLeft left) Q))))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight left) (Derivation.conjunctionRight right))
    (Derivation.conjunctionIntroduction forward backward))⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationEdgeProof
