module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- Inputs [type, original outer Context]. Context = Window × finite Boolean
 table and Window = symbols × types; these are the original product selectors. -/
def contextTypes : Program 1 := .composition InternalUnpair.right (fun _ : Fin 1 => InternalUnpair.left)
/-- Explicit source-member realization, not a replacement semantic predicate.
Malformed original Context rejects before the original finite-list membership.
No type decoder guard is added: original contextMemberValue tests raw type code. -/
def member (n : Nat) : Program 2 :=
  InternalAcceptance.branch
    (.composition (Continuation20261115.OriginalDecodedContextValidity.contextGuard n)
      (fun _ : Fin 1 => .projection 1))
    (constant 2 0)
    (.composition TwoSol20261113.CalibratedPrimary.Membership.contains
      ![.composition contextTypes (fun _ : Fin 1 => .projection 1),.projection 0])
/- W is not defined here. In particular the old image-calibrated raw head-window
program is not asserted to be the original allraw decoded head-window. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage
