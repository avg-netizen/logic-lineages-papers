module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualTargets
open UniformCertificateCompletion OriginalRootObservation
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual pre-minimum structural key; original decoded context and all typed
contexts. No source-membership or new representative-calibration premise. -/
def StructuralKey : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ∀ (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode c = some ctx →
  ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
  evaluate (rootObservation (OriginalStructuralClassKeyDefinitions.key p H G W))
    (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
      signatureNumber (NumberedHereditaryView.rootSignature ctx.1.1 ctx.1.2 q)

/-- Actual all-position refined tuple's GUARDED representative, not its bare
canonical traversal. Native specialization only, not internal cancellation. -/
def GuardedRepresentative : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  ∀ (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode c = some ctx →
  ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  evaluate (rootObservation (OriginalLambdaTraversalSelection.representative r.base r.window))
    (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
      signatureNumber (NumberedHereditaryView.rootSignature ctx.1.1 ctx.1.2 q)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualTargets
