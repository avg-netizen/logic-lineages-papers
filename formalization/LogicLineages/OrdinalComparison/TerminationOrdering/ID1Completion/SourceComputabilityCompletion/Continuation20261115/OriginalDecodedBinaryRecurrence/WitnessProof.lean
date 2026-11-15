module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.WitnessProof
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
open CoreProof

theorem at13 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 deps t3 t2 t1 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons v0 (Fin.cons t1 Fin.elim0)) _
  intro beta j Theta vals hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  have hd1j := InternalGraphCompositionFunctionalityProof.renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd1j
  have hd0j := InternalGraphCompositionFunctionalityProof.renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd0j
  have ha3j := InternalGraphCompositionFunctionalityProof.renameInto ha3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha3j
  have ha2j := InternalGraphCompositionFunctionalityProof.renameInto ha2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha2j
  have ha1j := InternalGraphCompositionFunctionalityProof.renameInto ha1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha1j
  exact CoreProof.atWitnesses n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) (d1.relabel j) (deps.relabel j) (t3.relabel j) (t2.relabel j) (t1.relabel j) vals hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hd1j hd0j ha3j ha2j ha1j hx

theorem at12 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 deps t3 t2 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons v1 (Fin.cons t2 Fin.elim0)) _
  intro beta j Theta t1 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  have hd1j := InternalGraphCompositionFunctionalityProof.renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd1j
  have hd0j := InternalGraphCompositionFunctionalityProof.renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd0j
  have ha3j := InternalGraphCompositionFunctionalityProof.renameInto ha3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha3j
  have ha2j := InternalGraphCompositionFunctionalityProof.renameInto ha2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha2j
  exact at13 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) (d1.relabel j) (deps.relabel j) (t3.relabel j) (t2.relabel j) t1 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hd1j hd0j ha3j ha2j hx

theorem at11 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 deps t3 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons v2 (Fin.cons t3 Fin.elim0)) _
  intro beta j Theta t2 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  have hd1j := InternalGraphCompositionFunctionalityProof.renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd1j
  have hd0j := InternalGraphCompositionFunctionalityProof.renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd0j
  have ha3j := InternalGraphCompositionFunctionalityProof.renameInto ha3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha3j
  exact at12 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) (d1.relabel j) (deps.relabel j) (t3.relabel j) t2 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hd1j hd0j ha3j hx

theorem at10 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 deps : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons v3 (Fin.cons z Fin.elim0)) _
  intro beta j Theta t3 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  have hd1j := InternalGraphCompositionFunctionalityProof.renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd1j
  have hd0j := InternalGraphCompositionFunctionalityProof.renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd0j
  exact at11 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) (d1.relabel j) (deps.relabel j) t3 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hd1j hd0j hx

theorem at9 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 d1 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons first (Fin.cons d1 Fin.elim0)) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  have hd1j := InternalGraphCompositionFunctionalityProof.renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd1j
  exact at10 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) (d1.relabel j) deps hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hd1j hx

theorem at8 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 d2 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons qb (Fin.cons d2 Fin.elim0)) _
  intro beta j Theta d1 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  have hd2j := InternalGraphCompositionFunctionalityProof.renameInto hd2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd2j
  exact at9 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) (d2.relabel j) d1 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hd2j hx

theorem at7 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 d3 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons ar (Fin.cons d3 Fin.elim0)) _
  intro beta j Theta d2 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  have hd3j := InternalGraphCompositionFunctionalityProof.renameInto hd3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hd3j
  exact at8 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) (d3.relabel j) d2 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hd3j hx

theorem at6 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 v3 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons last (Fin.cons z Fin.elim0)) _
  intro beta j Theta d3 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  have hv3j := InternalGraphCompositionFunctionalityProof.renameInto hv3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv3j
  exact at7 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) (v3.relabel j) d3 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hv3j hx

theorem at5 (source target sigma tau q a r b node first last param qb ar v0 v1 v2 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons last (Fin.cons param Fin.elim0)) _
  intro beta j Theta v3 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := InternalGraphCompositionFunctionalityProof.renameInto hv2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv2j
  exact at6 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) (v2.relabel j) v3 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hv2j hx

theorem at4 (source target sigma tau q a r b node first last param qb ar v0 v1 : OTerm alpha)
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
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons ar (Fin.cons param Fin.elim0)) _
  intro beta j Theta v2 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  have hv1j := InternalGraphCompositionFunctionalityProof.renameInto hv1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv1j
  exact at5 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) (v1.relabel j) v2 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hv1j hx

theorem at3 (source target sigma tau q a r b node first last param qb ar v0 : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) source sigma q a)))
    (ht : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) target tau r b)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp1 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) ar a r)))
    (hv0 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v0 first param)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons qb (Fin.cons param Fin.elim0)) _
  intro beta j Theta v1 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  have hv0j := InternalGraphCompositionFunctionalityProof.renameInto hv0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hv0j
  exact at4 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) (v0.relabel j) v1 hsj htj hnj hp0j hp3j hgj hp1j hp2j hv0j hx

theorem at2 (source target sigma tau q a r b node first last param qb ar : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) source sigma q a)))
    (ht : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) target tau r b)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp1 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) qb q b)))
    (hp2 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) ar a r)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons first (Fin.cons param Fin.elim0)) _
  intro beta j Theta v0 hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  have hp2j := InternalGraphCompositionFunctionalityProof.renameInto hp2 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp2j
  exact at3 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) (ar.relabel j) v0 hsj htj hnj hp0j hp3j hgj hp1j hp2j hx

theorem at1 (source target sigma tau q a r b node first last param qb : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) source sigma q a)))
    (ht : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) target tau r b)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hp1 : Nonempty (Derivation body Delta (graph2 (InternalPairing.pairing) qb q b)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalPairing.pairing) (Fin.cons a (Fin.cons r Fin.elim0)) _
  intro beta j Theta ar hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hp1j := InternalGraphCompositionFunctionalityProof.renameInto hp1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp1j
  exact at2 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) (qb.relabel j) ar hsj htj hnj hp0j hp3j hgj hp1j hx

theorem accepted (source target sigma tau q a r b node first last param : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) source sigma q a)))
    (ht : Nonempty (Derivation body Delta (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor) target tau r b)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)))
    (hp3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau q a r b first last param)) := by
  apply programCases (InternalPairing.pairing) (Fin.cons q (Fin.cons b Fin.elim0)) _
  intro beta j Theta qb hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hp0j := InternalGraphCompositionFunctionalityProof.renameInto hp0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp0j
  have hp3j := InternalGraphCompositionFunctionalityProof.renameInto hp3 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hp3j
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  exact at1 n arity cons (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (a.relabel j) (r.relabel j) (b.relabel j) (node.relabel j) (first.relabel j) (last.relabel j) (param.relabel j) qb hsj htj hnj hp0j hp3j hgj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.WitnessProof
