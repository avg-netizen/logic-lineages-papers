module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CoreProof
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
variable (n : Nat) (arity : Fin n → Nat) (cons : Bool)
attribute [local irreducible] programGraph
def rhs (sigma tau q a r b first last param : OTerm alpha) : Formula alpha :=
  eqn sigma tau ⊓
    ((eqn a b ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param) ⊔
     (eqn q r ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param))
def relation (node sigma tau q a r b first last param : OTerm alpha) : Formula alpha :=
  ((graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param).imp (rhs n arity sigma tau q a r b first last param)) ⊓
  ((rhs n arity sigma tau q a r b first last param).imp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))
theorem relationRename {beta : Type} (node sigma tau q a r b first last param : OTerm alpha) (j : alpha → beta) :
    (relation n arity node sigma tau q a r b first last param).relabel j =
      relation n arity (node.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) := by
  simp only [relation,rhs,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,StructuralExchangeFields.InternalProof.orRename,
    eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]

theorem atWitnesses (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 deps t3 t2 t1 vals : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) source sigma q a)))
    (ht : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) target tau r b)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp1 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) ar a r)))
    (hv0 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v0 first param)))
    (hv1 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v1 qb param)))
    (hv2 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v2 ar param)))
    (hv3 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v3 last param)))
    (hd3 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d3 last z)))
    (hd2 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d2 ar d3)))
    (hd1 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) d1 qb d2)))
    (hd0 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) deps first d1)))
    (ha3 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t3 v3 z)))
    (ha2 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t2 v2 t3)))
    (ha1 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) t1 v1 t2)))
    (ha0 : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) vals v0 t1)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  have hdep := DependenciesProof.four n cons source target sigma tau q a r b node param first qb ar last deps d1 d2 d3
    hs ht hn hg hp0 hp1 hp2 hp3 hd0 hd1 hd2 hd3
  have hmap := ValuesProof.orderedFour n arity param first qb ar last deps d1 d2 d3 v0 v1 v2 v3 vals t1 t2 t3
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
    have hc := (LayerProof.application n arity body alpha (E :: Delta) cons node vals param source target sigma tau q a r b v0 t1 v1 t2 v2 t3 v3 z
      (withHyp hg' E) (withHyp hn E) (withHyp hs E) (withHyp ht E) (withHyp ha0 E) (withHyp ha1 E) (withHyp ha2 E) (withHyp ha3 E)).mp hla
    have hf := andImp (identityImp (eqn sigma tau))
      (orImp (andImp (identityImp (eqn a b)) (ValuesProof.valueForward n arity first param v0 (withHyp hv0 E)))
        (andImp (identityImp (eqn q r)) (ValuesProof.valueForward n arity last param v3 (withHyp hv3 E))))
    obtain ⟨hout⟩ := applyImp hf hc
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let R := rhs n arity sigma tau q a r b first last param
    have hh : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := andImp (identityImp (eqn sigma tau))
      (orImp (andImp (identityImp (eqn a b)) (ValuesProof.valueBackward n arity first param v0 (withHyp hv0 R)))
        (andImp (identityImp (eqn q r)) (ValuesProof.valueBackward n arity last param v3 (withHyp hv3 R))))
    have hc := applyImp hf hh
    have hla := (LayerProof.application n arity body alpha (R :: Delta) cons node vals param source target sigma tau q a r b v0 t1 v1 t2 v2 t3 v3 z
      (withHyp hg' R) (withHyp hn R) (withHyp hs R) (withHyp ht R) (withHyp ha0 R) (withHyp ha1 R) (withHyp ha2 R) (withHyp ha3 R)).mpr hc
    obtain ⟨hout⟩ := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (R :: Delta)
      node param vals (numeral 1) (withHyp hans R)).mpr hla
    exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CoreProof
