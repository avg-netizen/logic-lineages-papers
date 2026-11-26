module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderContextCodecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The existing structural input is [source packed,target packed,parameter]. -/
def contextAt (n : Nat) : Program 3 :=
  .composition (OriginalDecodedContextValidity.contextGuard n)
    (fun _ : Fin 1 => InternalApplicationCertificateConstructors.leftOf (.projection 2))
def packedAt (n : Nat) (i : Fin 3) : Program 3 :=
  .composition (OriginalCodeValidityGuard.check n)
    (fun _ : Fin 1 => InternalApplicationCertificateConstructors.rightOf (.projection i))
/-- Literal original Context and RawPacked decoder validity, not typed acceptance. -/
def valid (n : Nat) : Program 3 :=
  InternalAcceptance.conjunction (contextAt n)
    (InternalAcceptance.conjunction (packedAt n 0) (packedAt n 1))
def contextCodeGuard (n : Nat) : Program 1 :=
  .composition (OriginalDecodedContextValidity.contextGuard n) (fun _ : Fin 1 => InternalUnpair.left)
/-- Accepted window projection; original failure default is raw zero. -/
def window (n : Nat) : Program 1 :=
  InternalAcceptance.branch (contextCodeGuard n) (InternalAcceptance.constantZero 1)
    (.composition InternalUnpair.left (fun _ : Fin 1 => InternalUnpair.left))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers
