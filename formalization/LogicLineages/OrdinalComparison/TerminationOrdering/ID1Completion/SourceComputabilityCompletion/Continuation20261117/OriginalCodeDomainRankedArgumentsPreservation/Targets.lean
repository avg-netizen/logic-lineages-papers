module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original Code-domain homogeneous typed-argument permutation transport.
BOTH original untyped syntax guards are retained, including canonical nil and
recursive child validity. These guards are supplied by actual decoded exchange,
not target typing. Same concrete H, context, M/W, fuel and permutation AST.
This is NOT the earlier unguarded allraw preservation proposal. -/
def InternalCodeDomainArgumentsPreserved : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (count types base target gamma context : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) base)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) target)) →
  Nonempty (Derivation body Delta
    (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.argumentsCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![types,base,gamma,context])) →
  Nonempty (Derivation body Delta
    (graph2 Continuation20261114.OriginalArgumentPermutation.check (suc z) base target)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.argumentsCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![types,target,gamma,context]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Targets
