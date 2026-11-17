module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInitialRepresentativeCoherence.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion TwoSol20261113.CalibratedPrimary
open Continuation20261114 Continuation20261115 Continuation20261116
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A NEW input tuple; no equality with the old p is asserted. -/
def alignedInputs (n : Nat) (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := { p.base with member := OriginalContextMemberLift.liftMember (OriginalUniverseDomainCoverage.member n) } }

def installedInputs (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  let H := OriginalConcreteHeadSignature.signature n arity
  let G := OriginalDecodedContextValidity.contextGuard n
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalCandidates.candidates n arity H
  let E := OriginalConcreteStructuralEdge.edge n arity
  let L := SeededPrimaryPool.primary T Q E
  let D := TransparentCandidate.candidate T
  OriginalRankGuardedRepresentative.transparentInputs H G (OriginalGuardedHeadSourceCoverage.window n arity)
    (Membership.inputs (alignedInputs n p) H G L D)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource
