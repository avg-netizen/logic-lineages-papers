module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open Continuation20261116
open OriginalUniverseDecoderInternalAcceptance
/-- Actual original term/argument acceptance alignment; member-inclusion oracle is discharged internally, not a premise. -/
def InternalConcreteMemberAlignment : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ raw gamma context : OTerm alpha),
  let H := OriginalConcreteHeadSignature.signature n arity
  let M := OriginalUniverseDomainCoverage.member n
  let W := OriginalGuardedHeadSourceCoverage.window n arity
  let ML := InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)
  Nonempty (Derivation body Delta
    (((TermAccepted H ML W typ raw gamma context).iff (TermAccepted H M W typ raw gamma context)) ⊓
      ((ArgumentsAccepted H ML W typ raw gamma context).iff (ArgumentsAccepted H M W typ raw gamma context))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.Targets
