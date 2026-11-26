module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNative
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual packed erasure at prefix length. Runtime context convention is
Encodable.encode (binders ++ sigma :: Gamma), mapped to Encodable.encode
(binders ++ Gamma); erased type is typeNumber sigma, not Encodable.encode sigma.
This definition changes no selected tuple, representative or class Program. -/
def erasedPacked (binders : List Ty) (sigma : Ty) (input : Nat) : Nat :=
  evaluate OriginalRawSyntaxTransport.erasePackedRaw
    (List.Vector.ofFn ![typeNumber sigma,binders.length,input])

/-- Native-only original class observers at arbitrary context prefix.
Only seed membership is supplied. Candidate/erased membership is derived;
sigma need not be in S. No internal arithmetic derivation or new observer
selection is asserted. -/
def PrefixErasedClassObserversLaw : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S binders Gamma : List Ty) (sigma : Ty)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (seed candidate : Nat),
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S (binders ++ sigma :: Gamma) seed = 1 →
  OriginalActiveClassKernelCalibrationSupportProof.rawClassValue n arity symbols S
    (binders ++ sigma :: Gamma) seed candidate = 1 →
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S (binders ++ Gamma)
      (erasedPacked binders sigma seed) = 1 ∧
    (InternalOriginalStepGuard.sourceValidityValue n arity symbols S (binders ++ Gamma)
        (erasedPacked binders sigma candidate) = 1 ∧
      (InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S (binders ++ Gamma)
          (erasedPacked binders sigma seed) =
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S (binders ++ Gamma)
          (erasedPacked binders sigma candidate) ∧
        evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
            (List.Vector.ofFn ![erasedPacked binders sigma seed]) =
          evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
            (List.Vector.ofFn ![erasedPacked binders sigma candidate])))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNative
