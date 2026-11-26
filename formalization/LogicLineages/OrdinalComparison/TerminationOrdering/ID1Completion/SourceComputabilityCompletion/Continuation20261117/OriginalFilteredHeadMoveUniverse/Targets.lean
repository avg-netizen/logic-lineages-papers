module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- Original Code-domain root headMove, restricted to actual filtered-primary endpoints.
All head tags are allowed; destination plain typing must be DERIVED, not premised. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (B : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate typ gamma context symbols types left right f g base target : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor left f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor right g target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ left)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ right)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed parameter)) →
  Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,target,symbols,types])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity))
      (numeral 1) ![typ,left,gamma,context])) →
  Nonempty (Derivation body Delta
    (graph2 (SeededPrimaryPool.primary
      (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
      (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (TypedPrimaryEdge.edge B))
      out seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.Membership.contains
      (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity))
      (numeral 1) ![typ,right,gamma,context]))

def InternalNumbered : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (B : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate typ gamma context symbols types left right label f g recorded base target extraTypes extras : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor left ![label,f,recorded,base,extraTypes,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor right ![label,g,recorded,target,extraTypes,extras])) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ left)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate typ right)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed parameter)) →
  Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,target,symbols,types])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity))
      (numeral 1) ![typ,left,gamma,context])) →
  Nonempty (Derivation body Delta
    (graph2 (SeededPrimaryPool.primary
      (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
      (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (TypedPrimaryEdge.edge B))
      out seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.Membership.contains
      (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity))
      (numeral 1) ![typ,right,gamma,context]))

def InternalFilteredHeadMoveUniverse : Prop := InternalOrdinary ∧ InternalNumbered
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Targets
