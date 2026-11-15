module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.DependenciesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

theorem atLists (source target sigma tau q r node child param deps qs rs : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode qs q z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rs r z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  have hc := ChildrenProof.rawOrdinary source target sigma tau q r qs rs child deps hs ht hq hr hp hd
  have hx := binaryValue NumericDependencyCross.rawDependencies OriginalDecodedDependencies.source OriginalDecodedDependencies.target
    deps source target ![node,param] hc
    (OriginalDecodedDependencies.SupportProof.sourceAt node param source target hn)
    (OriginalDecodedDependencies.SupportProof.targetAt node param source target hn)
  exact successorBranchIntro (OriginalDecodedDependencies.accepted n) (OriginalRawSyntaxTransport.constant 2 0)
    OriginalDecodedDependencies.decodedCross deps z ![node,param] (OriginalDecodedLambdaRecurrence.GuardProof.nodeRecover n node z param hg) hx

theorem atLeft (source target sigma tau q r node child param deps qs : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode qs q z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons r (Fin.cons z Fin.elim0)) _
  intro beta j Theta rs hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hqj
  exact atLists n (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (deps.relabel j) (qs.relabel j) rs hsj htj hnj hpj hgj hdj hqj hx

theorem singleton (source target sigma tau q r node child param deps : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons q (Fin.cons z Fin.elim0)) _
  intro beta j Theta qs hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [graph2Rename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact atLeft n (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (deps.relabel j) qs hsj htj hnj hpj hgj hdj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.DependenciesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.DependenciesProof
