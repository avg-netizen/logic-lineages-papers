module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.WitnessProof
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
open CoreProof

theorem at6 (source target f g base dest node child param symbols types ef eg rf rg value deps : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    (hrf : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rf f)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rg g)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param)))
    (hd : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) deps child z)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons value (Fin.cons z (Fin.elim0))) _
  intro beta j Theta vals hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hrfj := InternalGraphCompositionFunctionalityProof.renameInto hrf j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
  have hrgj := InternalGraphCompositionFunctionalityProof.renameInto hrg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrgj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact CoreProof.atWitnesses n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) (value.relabel j) (deps.relabel j) vals hsj htj hnj hpj hwj hgj hefj hegj hrfj hrgj hvj hdj hx

theorem at5 (source target f g base dest node child param symbols types ef eg rf rg value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    (hrf : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rf f)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rg g)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons child (Fin.cons z (Fin.elim0))) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hrfj := InternalGraphCompositionFunctionalityProof.renameInto hrf j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
  have hrgj := InternalGraphCompositionFunctionalityProof.renameInto hrg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrgj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact at6 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) (value.relabel j) deps hsj htj hnj hpj hwj hgj hefj hegj hrfj hrgj hvj hx

theorem at4 (source target f g base dest node child param symbols types ef eg rf rg : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    (hrf : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rf f)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rg g)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons child (Fin.cons param (Fin.elim0))) _
  intro beta j Theta value hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hrfj := InternalGraphCompositionFunctionalityProof.renameInto hrf j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
  have hrgj := InternalGraphCompositionFunctionalityProof.renameInto hrg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrgj
  exact at5 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) (rg.relabel j) value hsj htj hnj hpj hwj hgj hefj hegj hrfj hrgj hx

theorem at3 (source target f g base dest node child param symbols types ef eg rf : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    (hrf : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.headResult) rf f)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (OriginalHeadResult.headResult) (Fin.cons g (Fin.elim0)) _
  intro beta j Theta rg hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  have hrfj := InternalGraphCompositionFunctionalityProof.renameInto hrf j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrfj
  exact at4 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) (eg.relabel j) (rf.relabel j) rg hsj htj hnj hpj hwj hgj hefj hegj hrfj hx

theorem at2 (source target f g base dest node child param symbols types ef eg : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) eg g)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (OriginalHeadResult.headResult) (Fin.cons f (Fin.elim0)) _
  intro beta j Theta rf hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  have hegj := InternalGraphCompositionFunctionalityProof.renameInto heg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hegj
  exact at3 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) (eg.relabel j) rf hsj htj hnj hpj hwj hgj hefj hegj hx

theorem at1 (source target f g base dest node child param symbols types ef : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hef : Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.encodeHead) ef f)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (OriginalHeadEncodingBridge.encodeHead) (Fin.cons g (Fin.elim0)) _
  intro beta j Theta eg hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hefj := InternalGraphCompositionFunctionalityProof.renameInto hef j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hefj
  exact at2 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) (ef.relabel j) eg hsj htj hnj hpj hwj hgj hefj hx

theorem accepted (source target f g base dest node child param symbols types : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  apply programCases (OriginalHeadEncodingBridge.encodeHead) (Fin.cons f (Fin.elim0)) _
  intro beta j Theta ef hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hwj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  exact at1 n arity (source.relabel j) (target.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) ef hsj htj hnj hpj hwj hgj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.WitnessProof
