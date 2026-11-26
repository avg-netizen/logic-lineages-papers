module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasuredBaseScratchProof
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
open NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof (exact_OpenSelectedGrammarTypeLeafScratch)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeafSharedMeasureProof (exact_OpenCoverTypeLeafSharedMeasure)
open NumberedWindowInternalCoverTypeLeafMeasureTargets

/-- Tag-three local placement without a supplied measurement pair. The
actual settings type membership remains independent and explicit. -/
theorem exact_OpenCoverTypeLeafMeasuredBaseScratch (V M : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (p vertices ty : OTerm α)
    (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (typeLeafTerm ty))))
    (measured : Nonempty (Derivation body Γ (unary (typeLeafSharedMeasure M) p (typeLeafTerm ty))))
    (held : Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V (typeLeafSharedMeasure M)) s) vertices (typeLeafTerm ty)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (typeLeafTerm ty))) :=
  exact_OpenSelectedGrammarTypeLeafScratch V (typeLeafSharedMeasure M) s body α Γ p z z vertices ty
    member valid measured (exact_OpenCoverTypeLeafSharedMeasure M body α Γ ty p measured) held

#print axioms exact_OpenCoverTypeLeafMeasuredBaseScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasuredBaseScratchProof
