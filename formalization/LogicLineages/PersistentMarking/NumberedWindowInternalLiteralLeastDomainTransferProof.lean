module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastDomainTransferProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)
open NumberedWindowInternalLiteralCoveredMemoLeastProof (exact_OpenLeastFromCoverage)
open NumberedWindowInternalLiteralLeastCoverageProof (exact_OpenCoverageFromLeast)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The original covered raw packet and the newly forming packet use
the same context parser and vertex cover. A successful true least
domain therefore transfers to the new actual window program even
when the least values, exchange and window programs are not identified. -/
theorem exact_OpenLiteralLeastDomainTransfer (C : Program 3) (X X' : Program 2) (W W' : Program 3)
    (s : Settings) (ctx ty raw : OTerm α) (old : D B Γ (hasLeast C X W s ctx ty raw)) :
    D B Γ (hasLeast C X' W' s ctx ty raw) := by
  apply casesLeast C X W s ctx ty raw (hasLeast C X' W' s ctx ty raw) old
  intro β j Δ selected keep got
  rw [hasRename]
  have covered := exact_OpenCoverageFromLeast C X W s (ctx.relabel j) (ty.relabel j)
    (raw.relabel j) selected got
  exact exact_OpenLeastFromCoverage C X' W' s (ctx.relabel j) (ty.relabel j) (raw.relabel j) covered

#print axioms exact_OpenLiteralLeastDomainTransfer
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastDomainTransferProof
