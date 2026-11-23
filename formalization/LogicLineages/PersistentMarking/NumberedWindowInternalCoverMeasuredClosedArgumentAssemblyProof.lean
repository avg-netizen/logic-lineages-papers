module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentAssemblyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScalarEdge (edgeGraph exchangeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareShared)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange thinSwapExchange)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swapAccept (p : Program 2) (a b : OTerm α)
    (rev : Nonempty (Derivation body Γ (programGraph p (suc z) (exchangeTape b a)))) :
    Nonempty (Derivation body Γ
      (programGraph (thinSwapExchange p) (suc z) (exchangeTape a b))) := by
  apply compositionValue p ![.projection 1,.projection 0] (suc z) (exchangeTape a b) ![b,a] rev
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact projectionValue 1 (exchangeTape a b)
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 0 (exchangeTape a b)

/-- Compose genuine directed reports with the original measure, cover,
and window guards. Both orientations are independently supplied. -/
theorem exact_OpenPairedMeasuredEdgeFromReports (C W : Program 3) (s : Settings)
    (D : Program 2) (M : Program 1) (ctx ty a b m cover : OTerm α)
    (aw : Nonempty (Derivation body Γ (windowAt W ctx ty a)))
    (bw : Nonempty (Derivation body Γ (windowAt W ctx ty b)))
    (am : Nonempty (Derivation body Γ (unary M m a)))
    (bm : Nonempty (Derivation body Γ (unary M m b)))
    (ac : Nonempty (Derivation body Γ (unary (coverOption C s) (suc cover) a)))
    (bc : Nonempty (Derivation body Γ (unary (coverOption C s) (suc cover) b)))
    (ab : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape a b))))
    (ba : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape b a)))) :
    Nonempty (Derivation body Γ
      (edgeGraph (guardedExchange C s (thinPairedExchange (measuredExchange M D))) W ctx ty a b)) := by
  let Dm := measuredExchange M D
  let X := guardedExchange C s (thinPairedExchange Dm)
  have abm : Nonempty (Derivation body Γ (programGraph Dm (suc z) (exchangeTape a b))) :=
    conjunctionAccept D (compareMeasurements M) (exchangeTape a b) ab (compareShared M a b m am bm)
  have bam : Nonempty (Derivation body Γ (programGraph Dm (suc z) (exchangeTape b a))) :=
    conjunctionAccept D (compareMeasurements M) (exchangeTape b a) ba (compareShared M b a m bm am)
  have pair := conjunctionAccept Dm (thinSwapExchange Dm) (exchangeTape a b) abm
    (swapAccept Dm a b bam)
  have coverEq : Nonempty (Derivation body Γ (programGraph (compareOptions C s) (suc z) (exchangeTape a b))) :=
    compareShared (coverOption C s) a b (suc cover) ac bc
  obtain ⟨guard⟩ := conjunctionAccept (thinPairedExchange Dm) (compareOptions C s) (exchangeTape a b)
    pair coverEq
  obtain ⟨aWindow⟩ := aw
  obtain ⟨bWindow⟩ := bw
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx ty a b
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight law)
    (Derivation.conjunctionIntroduction guard (Derivation.conjunctionIntroduction aWindow bWindow))⟩

#print axioms exact_OpenPairedMeasuredEdgeFromReports
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentAssemblyProof
