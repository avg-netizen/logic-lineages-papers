module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115 Continuation20261116

/-- Joint induction endpoint for the actual original relation. Target plain typing
is an explicit invariant premise, to be discharged at the filtered primary caller. -/
def InternalTerm : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ source target gamma context symbols types window node : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context)) →
  Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false typ source gamma context)) →
  Nonempty (Derivation body Delta
    (OriginalTypedDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      false typ target gamma)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false typ target gamma context))

def InternalArguments : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ source target gamma context symbols types window node : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context)) →
  Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      true typ source gamma context)) →
  Nonempty (Derivation body Delta
    (OriginalTypedDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      true typ target gamma)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      true typ target gamma context))

def InternalPlainAwareExchangeUniverse : Prop := InternalTerm ∧ InternalArguments
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Targets
