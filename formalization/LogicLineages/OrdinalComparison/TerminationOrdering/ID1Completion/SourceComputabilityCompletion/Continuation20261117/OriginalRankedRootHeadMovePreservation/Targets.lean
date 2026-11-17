module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original ordinary ranked-root headMove branch. The destination head is
arbitrary. Its identity and both argument-child Code guards must be derived
from the actual headMove/root guards, not supplied. -/
def InternalOrdinaryRankedHeadMove : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right f g base target typ gamma context symbols windowTypes : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 OriginalRawSyntaxTransport.ordinaryConstructor left f base)) →
  Nonempty (Derivation body Delta
    (graph2 OriginalRawSyntaxTransport.ordinaryConstructor right g target)) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 5) f)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta
    (programGraph (Continuation20261114.OriginalHeadMove.headMove n arity) (suc z)
      ![f,base,g,target,symbols,windowTypes])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![typ,left,gamma,context])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![typ,right,gamma,context]))

/-- Original numbered ranked-root headMove branch. All unchanged label,
recorded type, extra-type list and extra arguments are literally shared, as in
codeExchange. No target argument or term success is a premise. -/
def InternalNumberedRankedHeadMove : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right label f g recorded base target extraTypes extras typ gamma context symbols windowTypes : OTerm alpha),
  Nonempty (Derivation body Delta
    (programGraph OriginalRawSyntaxTransport.numberedConstructor left
      ![label,f,recorded,base,extraTypes,extras])) →
  Nonempty (Derivation body Delta
    (programGraph OriginalRawSyntaxTransport.numberedConstructor right
      ![label,g,recorded,target,extraTypes,extras])) →
  Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 5) f)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) left)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) right)) →
  Nonempty (Derivation body Delta
    (programGraph (Continuation20261114.OriginalHeadMove.headMove n arity) (suc z)
      ![f,base,g,target,symbols,windowTypes])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![typ,left,gamma,context])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.termCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![typ,right,gamma,context]))

/-- One coherent original ranked-root caller bridge, with both original forms. -/
def InternalRankedRootHeadMoves : Prop :=
  InternalOrdinaryRankedHeadMove ∧ InternalNumberedRankedHeadMove
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Targets
