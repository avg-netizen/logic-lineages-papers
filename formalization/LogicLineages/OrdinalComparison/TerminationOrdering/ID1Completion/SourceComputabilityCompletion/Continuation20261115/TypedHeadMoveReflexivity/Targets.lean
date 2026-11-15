module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Original permutation checker reflexivity from original typed acceptance;
no extraction output or successful option witness is assumed. -/
def InternalPermutation : Prop := ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (Delta : List (Formula alpha)) (argumentTypes base gamma : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H argumentTypes base gamma)) →
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base base))

/-- Exact original constructor-family self-edges. Typed spine acceptance replaces
the formerly public Some-extraction premise, discharged internally. Original
window and head constructor evidence, and unary ArrowClosed, are retained. -/
def InternalBasic : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha)) (which : Fin 2) (raw base symbols types argumentTypes gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral (RawHeadWindowCoverage.basicTag which)) (numeral 0))) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H argumentTypes base gamma)) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalUnary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha)) (which : Fin 2) (raw payload base symbols types argumentTypes gamma : OTerm alpha),
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral (RawHeadWindowCoverage.unaryTag which)) payload)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H argumentTypes base gamma)) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalApplication : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha)) (raw payload sigma tau base symbols types argumentTypes gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H argumentTypes base gamma)) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalRanked : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (H : Program 1)
    (alpha : Type) (Delta : List (Formula alpha)) (raw symbol base symbols types argumentTypes gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) symbol)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (OriginalTypedDecoderInternalAcceptance.ArgumentsAccepted H argumentTypes base gamma)) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedHeadMoveReflexivity.Targets
