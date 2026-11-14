module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original ordinary recursive-child branch, no headMove oracle. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source head base symbols types tail : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source source)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source head base)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code (numeral 1) tail)) →
  Nonempty (Derivation body Delta (graph3 (ConcreteHeadMoveLayer.layer n arity V) (numeral 2) node code param))

/-- Original numbered recursive-base branch uses diagonal answer position 0,
not a neighboring cross answer; the full four-answer list is retained. -/
def InternalNumbered : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source k head tau base ts extras symbols types t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source source)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,head,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code (numeral 1) t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  Nonempty (Derivation body Delta (graph3 (ConcreteHeadMoveLayer.layer n arity V) (numeral 2) node code param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.Targets
