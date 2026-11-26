module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.ComparatorGate
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open Continuation20261116
open OriginalUniverseDecoderInternalAcceptance
theorem exactConcreteMemberAlignment : Targets.InternalConcreteMemberAlignment ↔
  (∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ raw gamma context : OTerm alpha),
  let H := OriginalConcreteHeadSignature.signature n arity
  let M := OriginalUniverseDomainCoverage.member n
  let W := OriginalGuardedHeadSourceCoverage.window n arity
  let ML := InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)
  Nonempty (Derivation body Delta
    (((TermAccepted H ML W typ raw gamma context).iff (TermAccepted H M W typ raw gamma context)) ⊓
      ((ArgumentsAccepted H ML W typ raw gamma context).iff (ArgumentsAccepted H M W typ raw gamma context))))) := Iff.rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.ComparatorGate
