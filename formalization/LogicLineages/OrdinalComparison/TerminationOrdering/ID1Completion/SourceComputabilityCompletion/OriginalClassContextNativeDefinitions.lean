module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeDefinitions
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original raw Object erasure, observed at its packed output. This
retains the actual extended/parent contexts and original packed coding. -/
def erasedPacked (Gamma : List Ty) (sigma : Ty) (input : Nat) : Nat :=
  (Nat.unpair (evaluate eraseObjectRaw (List.Vector.ofFn ![
    ContextUniform.objectCode (sigma :: Gamma) input]))).2

/-- Original class hits in a genuine extended context preserve BOTH the
original erased representative key and the erased variable-rank observer.
Source-universe membership is supplied only for the seed and derived for
candidate and both erased terms. No membership of sigma in S is assumed. -/
def ErasedClassObserversLaw : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma : Ty)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (seed candidate : Nat),
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S (sigma :: Gamma) seed = 1 →
  OriginalActiveClassKernelCalibrationSupportProof.rawClassValue n arity symbols S
    (sigma :: Gamma) seed candidate = 1 →
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma
      (erasedPacked Gamma sigma seed) = 1 ∧
    (InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma
        (erasedPacked Gamma sigma candidate) = 1 ∧
      (InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
          (erasedPacked Gamma sigma seed) =
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
          (erasedPacked Gamma sigma candidate) ∧
        evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
            (List.Vector.ofFn ![erasedPacked Gamma sigma seed]) =
          evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
            (List.Vector.ofFn ![erasedPacked Gamma sigma candidate])))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeDefinitions
