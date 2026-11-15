module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph

def rhs (sigma tau child param : OTerm alpha) : Formula alpha :=
  eqn sigma tau ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param
def relation (node sigma tau child param : OTerm alpha) : Formula alpha :=
  ((graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param).imp (rhs n arity sigma tau child param)) ⊓
  ((rhs n arity sigma tau child param).imp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))
theorem relationRename {beta : Type} (node sigma tau child param : OTerm alpha) (j : alpha → beta) :
    (relation n arity node sigma tau child param).relabel j =
      relation n arity (node.relabel j) (sigma.relabel j) (tau.relabel j) (child.relabel j) (param.relabel j) := by
  simp only [relation,rhs,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]

theorem atWitnesses (source target sigma tau q r node child param value deps vals : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode vals value z)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau child param)) := by
  have hdep := DependenciesProof.singleton n source target sigma tau q r node child param deps hs ht hn hp hg hd
  have hmap := OriginalDecodedExchangeEquation.StepProof.consValue n arity deps child z param value z vals
    hd hv (OriginalDecodedExchangeEquation.StepProof.nilValue n arity param) ha
  have hans : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) vals node param)) :=
    binaryValue (OriginalDecodedExchangeEquation.answerMap n arity) (OriginalDecodedDependencies.dependencies n) (.projection 1)
      vals deps param ![node,param] hmap hdep (projectionValue 1 ![node,param])
  have hg' := GuardProof.answerTransport n node z vals param hg
  apply andIntro
  · let E := graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hla := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (E :: Delta)
      node param vals (numeral 1) (withHyp hans E)).mp he
    have hc := (LayerProof.lambda n arity node vals param source target sigma tau q r value z
      (withHyp hg' E) (withHyp hn E) (withHyp hs E) (withHyp ht E) (withHyp ha E)).mp hla
    have hchild := outputTransport (OriginalDecodedExchangeEquation.exchange n arity) value (numeral 1)
      ![child,param] (andRight hc) (withHyp hv E)
    obtain ⟨hout⟩ := andIntro (andLeft hc) hchild
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let R := rhs n arity sigma tau child param
    have hh : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique (OriginalDecodedExchangeEquation.exchange n arity) value (numeral 1)
      ![child,param] (withHyp hv R) (andRight hh)
    have hla := (LayerProof.lambda n arity node vals param source target sigma tau q r value z
      (withHyp hg' R) (withHyp hn R) (withHyp hs R) (withHyp ht R) (withHyp ha R)).mpr (andIntro (andLeft hh) he)
    obtain ⟨hout⟩ := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (R :: Delta)
      node param vals (numeral 1) (withHyp hans R)).mpr hla
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem atDeps (source target sigma tau q r node child param value deps : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau child param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons value (Fin.cons z Fin.elim0)) _
  intro beta j Theta vals hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
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
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact atWitnesses n arity (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (value.relabel j) (deps.relabel j) vals hsj htj hnj hpj hgj hvj hdj hx

theorem atValue (source target sigma tau q r node child param value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau child param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons child (Fin.cons z Fin.elim0)) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
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
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact atDeps n arity (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) (value.relabel j) deps hsj htj hnj hpj hgj hvj hx

theorem accepted (source target sigma tau q r node child param : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)))
    : Nonempty (Derivation body Delta (relation n arity node sigma tau child param)) := by
  apply programCases (OriginalDecodedExchangeEquation.exchange n arity) (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta value hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  rw [relationRename]
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
  exact atValue n arity (source.relabel j) (target.relabel j) (sigma.relabel j) (tau.relabel j) (q.relabel j) (r.relabel j) (node.relabel j) (child.relabel j) (param.relabel j) value hsj htj hnj hpj hgj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.CoreProof
