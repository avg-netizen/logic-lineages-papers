module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafStrictWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasuredBaseScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafTypedMeasuredScratchProof
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
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalCoverTypeLeafStrictWindowProof (exact_OpenCoverTypeLeafStrictWindowK)
open NumberedWindowInternalCoverTypeLeafMeasuredBaseScratchProof (exact_OpenCoverTypeLeafMeasuredBaseScratch)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets

/-- Literal tag three with actual K and successor-width premises paid
inside the proof, on the two explicitly reselected programs and their
same original physical scratch. -/
theorem exact_OpenCoverTypeLeafTypedMeasuredScratch
    (V M : Program 1) (s : Settings) (B : Program 2) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx result p vertices ty : OTerm α)
    (typed : Nonempty (Derivation body Γ (windowGraph (leafStrictWindow s B T) ctx result (typeLeafTerm ty))))
    (valid : Nonempty (Derivation body Γ (unary V (suc z) (typeLeafTerm ty))))
    (measured : Nonempty (Derivation body Γ (unary (typeLeafSharedMeasure M) p (typeLeafTerm ty))))
    (held : Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V (typeLeafSharedMeasure M)) s) vertices (typeLeafTerm ty)))) :
    Nonempty (Derivation body Γ (memberGraph vertices (typeLeafTerm ty))) :=
  exact_OpenCoverTypeLeafMeasuredBaseScratch V M s body α Γ p vertices ty
    (exact_OpenCoverTypeLeafStrictWindowK s B T body α Γ ctx ty result typed) valid measured held

#print axioms exact_OpenCoverTypeLeafTypedMeasuredScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafTypedMeasuredScratchProof
