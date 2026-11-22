module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof (exact_OpenCoverCombinedRestrictedPairedAux)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverProof (exact_OpenCoverThinCrossCover)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets

theorem exact_OpenCoverCombinedRestrictedPairedCrossCover : ExactOpenCoverCombinedRestrictedPairedCrossCover := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal P W D X a b syn ty argument
    fg gf ma mb k
  apply exact_OpenCoverCombinedRestrictedPairedAux V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal
    syn ty argument fg gf ma mb
  intro β j Δ vertices keep ca cb edge
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge X W body β Δ (ctx.relabel j) (cod.relabel j)
    (a.relabel j) (b.relabel j)
  obtain ⟨edge⟩ := edge
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft law) edge
  have windows := Derivation.conjunctionRight calls
  have both := exact_OpenCoverThinCrossCover P.cover P.W P.V s body β Δ (ctx.relabel j) (cod.relabel j)
    (a.relabel j) (b.relabel j) vertices ⟨Derivation.conjunctionLeft windows⟩
    ⟨Derivation.conjunctionRight windows⟩ ca cb
  exact k β j Δ vertices keep both ⟨edge⟩

#print axioms exact_OpenCoverCombinedRestrictedPairedCrossCover
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof
