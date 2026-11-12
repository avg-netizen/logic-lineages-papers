module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open UniformCertificateCompletion OriginalRawObjectTransport OriginalErasureCertificateContinuation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalVariableCertificateEndpoint : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premise p H G W context tau source target witness gamma extended packed raw domain index).imp
      (EndpointResult tau source target extended)))

def ActualOriginalSuccessorVariableErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premise p H G W context tau source target witness gamma extended packed raw domain (suc index) ⊓
      (graph1 eraseObjectRaw erasedSource source ⊓ graph1 eraseObjectRaw erasedTarget target)).imp
      (SurvivorResult tau source target gamma extended index erasedSource erasedTarget)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationTargets
