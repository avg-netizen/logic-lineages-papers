module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasuredScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof (exact_OpenSelectedGrammarNamedLeafScratch)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafSharedMeasureProof (exact_OpenCoverNamedLeafSharedMeasure)
open NumberedWindowInternalCoverNamedLeafMeasureTargets

/-- The actual index itself determines width at this same chosen observation,
with no independently supplied pair or index-bound witness. -/
theorem exact_OpenCoverNamedLeafMeasuredScratch (b : Bool) (V M : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (p vertices ty i : OTerm α)
    (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (namedTerm b.toNat ty i))))
    (measured : Nonempty (Derivation body Γ (unary (namedSharedMeasure M) p (namedTerm b.toNat ty i))))
    (held : Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V (namedSharedMeasure M)) s) vertices (namedTerm b.toNat ty i)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (namedTerm b.toNat ty i))) := by
  have exactBounds := exact_OpenCoverNamedLeafSharedMeasure b M body α Γ ty i p measured
  exact exact_OpenSelectedGrammarNamedLeafScratch b V (namedSharedMeasure M) s body α Γ p z i vertices ty i
    member exactBounds.2 valid measured exactBounds.1 held

#print axioms exact_OpenCoverNamedLeafMeasuredScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasuredScratchProof
