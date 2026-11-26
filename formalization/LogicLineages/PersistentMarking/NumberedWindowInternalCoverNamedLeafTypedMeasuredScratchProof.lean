module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafGrammarWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasuredScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafTypedMeasuredScratchProof
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
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverNamedLeafGrammarWindowProof (exact_OpenCoverNamedLeafGrammarWindowK)
open NumberedWindowInternalCoverNamedLeafMeasuredScratchProof (exact_OpenCoverNamedLeafMeasuredScratch)

/-- The actual index itself determines width at this same chosen observation,
with no independently supplied pair or index-bound witness. -/
theorem exact_OpenCoverNamedLeafTypedMeasuredScratch (b : Bool) (V M : Program 1) (s : Settings)
    (B : Program 2) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx result p vertices ty i : OTerm α)
    (typed : Nonempty (Derivation body Γ (windowGraph (namedGrammarWindow s B T) ctx result (namedTerm b.toNat ty i))))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (namedTerm b.toNat ty i))))
    (measured : Nonempty (Derivation body Γ (unary (namedSharedMeasure M) p (namedTerm b.toNat ty i))))
    (held : Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V (namedSharedMeasure M)) s) vertices (namedTerm b.toNat ty i)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (namedTerm b.toNat ty i))) := by
  exact exact_OpenCoverNamedLeafMeasuredScratch b V M s body α Γ p vertices ty i
    (exact_OpenCoverNamedLeafGrammarWindowK b s B T body α Γ ctx ty i result typed) valid measured held

#print axioms exact_OpenCoverNamedLeafTypedMeasuredScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafTypedMeasuredScratchProof
