module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.NumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open TransparentHeadBranches.Proof (identityImp andImp orImp applyImp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph
def rhs (k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types : OTerm alpha) : Formula alpha :=
  ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
    (((eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]) ⊔
      ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g ⊓ eqn extras otherExtras) ⊓
        graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param)) ⊔
     ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g ⊓ eqn base dest) ⊓
       graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param)))
def relation (node k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types : OTerm alpha) : Formula alpha :=
  ((graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param).imp (rhs n arity k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types)) ⊓
  ((rhs n arity k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types).imp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))
theorem relationRename {beta : Type} (node k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types : OTerm alpha) (j : alpha → beta) :
    (relation n arity node k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types).relabel j =
      relation n arity (node.relabel j) (k.relabel j) (l.relabel j) (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j) (ts.relabel j) (us.relabel j) (extras.relabel j) (otherExtras.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) := by
  simp only [relation,rhs,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,
    StructuralExchangeFields.InternalProof.orRename,eqnRelabel,graph2Rename,
    ConcreteHeadMoveLayer.SyntaxProof.sixRename,GuardedSourceSyntaxProof.numeralRename]

theorem atWitnesses (source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types ef eg middle1 middle2 v0 v1 v2 v3 d3 d2 d1 deps t3 t2 t1 vals : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source ![k,f,tau,base,ts,extras])))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target ![l,g,upsilon,dest,us,otherExtras])))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first base dest)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last extras otherExtras)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    (hp1 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) middle1 base otherExtras)))
    (hp2 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) middle2 extras dest)))
    (hv0 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v0 first param)))
    (hv1 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v1 middle1 param)))
    (hv2 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v2 middle2 param)))
    (hv3 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v3 last param)))
    (hd3 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d3 last z)))
    (hd2 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d2 middle2 d3)))
    (hd1 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d1 middle1 d2)))
    (hd0 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) deps first d1)))
    (ha3 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t3 v3 z)))
    (ha2 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t2 v2 t3)))
    (ha1 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t1 v1 t2)))
    (ha0 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) vals v0 t1)))
    : Nonempty (Derivation body Delta (relation n arity node k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types)) := by
  have hdep := DependenciesProof.four n source target k l f g tau upsilon ts us base extras dest otherExtras node param first middle1 middle2 last deps d1 d2 d3
    hs ht hn hg hp0 hp1 hp2 hp3 hd0 hd1 hd2 hd3
  have hmap := OriginalDecodedBinaryRecurrence.ValuesProof.orderedFour n arity param first middle1 middle2 last deps d1 d2 d3 v0 v1 v2 v3 vals t1 t2 t3
    hd0 hd1 hd2 hd3 ha0 ha1 ha2 ha3 hv0 hv1 hv2 hv3
  have hans : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) vals node param)) :=
    binaryValue (OriginalDecodedExchangeEquation.answerMap n arity) (OriginalDecodedDependencies.dependencies n) (.projection 1)
      vals deps param ![node,param] hmap hdep (projectionValue 1 ![node,param])
  have hg' := OriginalDecodedLambdaRecurrence.GuardProof.answerTransport n node z vals param hg
  apply andIntro
  · let E := graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hla := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (E :: Delta)
      node param vals (numeral 1) (withHyp hans E)).mp he
    have hc := (ConcreteHeadMoveLayer.NumberedProof.internalNumbered n arity body alpha (E :: Delta)
      (OriginalDecodedLayerCalibration.guard n) node vals param source target k l f g tau upsilon base dest ts us extras otherExtras ef eg symbols types v0 t1 v1 t2 v2 t3 v3 z
      (withHyp hg' E) (withHyp hn E) (withHyp hw E) (withHyp hs E) (withHyp ht E)
      (withHyp hef E) (withHyp heg E) (withHyp ha0 E) (withHyp ha1 E) (withHyp ha2 E) (withHyp ha3 E)).mp hla
    have hf := andImp (identityImp (eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)))
      (orImp
        (orImp (identityImp (eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]))
          (andImp (andImp (OriginalDecodedOrdinaryRecurrence.EqualityProof.forward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef E) (withHyp heg E)) (identityImp (eqn extras otherExtras))) (OriginalDecodedBinaryRecurrence.ValuesProof.valueForward n arity first param v0 (withHyp hv0 E))))
        (andImp (andImp (OriginalDecodedOrdinaryRecurrence.EqualityProof.forward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef E) (withHyp heg E)) (identityImp (eqn base dest))) (OriginalDecodedBinaryRecurrence.ValuesProof.valueForward n arity last param v3 (withHyp hv3 E))))
    obtain ⟨hout⟩ := applyImp hf hc
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let R := rhs n arity k l f g tau upsilon base dest ts us extras otherExtras first last param symbols types
    have hh : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := andImp (identityImp (eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)))
      (orImp
        (orImp (identityImp (eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]))
          (andImp (andImp (OriginalDecodedOrdinaryRecurrence.EqualityProof.backward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef R) (withHyp heg R)) (identityImp (eqn extras otherExtras))) (OriginalDecodedBinaryRecurrence.ValuesProof.valueBackward n arity first param v0 (withHyp hv0 R))))
        (andImp (andImp (OriginalDecodedOrdinaryRecurrence.EqualityProof.backward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef R) (withHyp heg R)) (identityImp (eqn base dest))) (OriginalDecodedBinaryRecurrence.ValuesProof.valueBackward n arity last param v3 (withHyp hv3 R))))
    have hc := applyImp hf hh
    have hla := (ConcreteHeadMoveLayer.NumberedProof.internalNumbered n arity body alpha (R :: Delta)
      (OriginalDecodedLayerCalibration.guard n) node vals param source target k l f g tau upsilon base dest ts us extras otherExtras ef eg symbols types v0 t1 v1 t2 v2 t3 v3 z
      (withHyp hg' R) (withHyp hn R) (withHyp hw R) (withHyp hs R) (withHyp ht R)
      (withHyp hef R) (withHyp heg R) (withHyp ha0 R) (withHyp ha1 R) (withHyp ha2 R) (withHyp ha3 R)).mpr hc
    obtain ⟨hout⟩ := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (R :: Delta)
      node param vals (numeral 1) (withHyp hans R)).mpr hla
    exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.CoreProof
