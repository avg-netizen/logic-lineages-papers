module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)

/-- Actual self-head-class acceptance, not native head equivalence. -/
def InternalClass : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalHeadClass.equivalent (numeral 1) raw raw))

def InternalBasic : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (which : Fin 2) (raw base list symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral (RawHeadWindowCoverage.basicTag which)) (numeral 0))) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalUnary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (which : Fin 2) (raw payload base list symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral (RawHeadWindowCoverage.unaryTag which)) payload)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalApplication : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw payload sigma tau base list symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 4) payload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload sigma tau)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))

def InternalRanked : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw symbol base list symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 5) symbol)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))) →
  Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
    ![raw,base,raw,base,symbols,types]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMoveReflexivity.Targets
