module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original numbered equation, all raw metadata/child fields derived from actual
constructors. Only original headMove remains an opaque field graph premise. -/
def InternalNumbered : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param source target k l f g tau upsilon base dest ts us extras otherExtras
      ef eg move h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source
    ![k,f,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target
    ![l,g,upsilon,dest,us,otherExtras])) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph3 (U 16) move node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta
      (graph3 (ResultStructuralFields.layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
     (((eqn extras otherExtras ⊓ eqn move (numeral 1)) ⊔
       ((eqn ef eg ⊓ eqn extras otherExtras) ⊓ eqn h0 (numeral 1))) ⊔
      ((eqn ef eg ⊓ eqn base dest) ⊓ eqn h3 (numeral 1))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Targets
