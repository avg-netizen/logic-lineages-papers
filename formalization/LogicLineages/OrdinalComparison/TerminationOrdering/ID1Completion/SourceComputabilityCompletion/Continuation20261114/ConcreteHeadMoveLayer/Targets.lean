module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source target f g base dest ef eg rf rg symbolsCode typesCode h0 t0 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbolsCode typesCode)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rf f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rg g)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  (Nonempty (Derivation body Delta (graph3 (layer n arity V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta
     ((programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbolsCode,typesCode] ⊓ eqn rg rf) ⊔ (eqn ef eg ⊓ eqn h0 (numeral 1)))))

def InternalNumbered : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source target k l f g tau upsilon base dest ts us extras otherExtras
      ef eg symbolsCode typesCode h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbolsCode typesCode)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source
    ![k,f,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target
    ![l,g,upsilon,dest,us,otherExtras])) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta
      (graph3 (layer n arity V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
     (((eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbolsCode,typesCode]) ⊔
       ((eqn ef eg ⊓ eqn extras otherExtras) ⊓ eqn h0 (numeral 1))) ⊔
      ((eqn ef eg ⊓ eqn base dest) ⊓ eqn h3 (numeral 1))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Targets
