module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.DependenciesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.CoreProof
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
def rhs (f g base dest child param symbols types : OTerm alpha) : Formula alpha :=
  ((programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types] ⊓ graph2 resultEqual (numeral 1) g f) ⊔
    (graph2 encodedEqual (numeral 1) f g ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param))
def relation (node f g base dest child param symbols types : OTerm alpha) : Formula alpha :=
  ((graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param).imp (rhs n arity f g base dest child param symbols types)) ⊓
  ((rhs n arity f g base dest child param symbols types).imp (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))
theorem relationRename {beta : Type} (node f g base dest child param symbols types : OTerm alpha) (j : alpha → beta) :
    (relation n arity node f g base dest child param symbols types).relabel j =
      relation n arity (node.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (dest.relabel j) (child.relabel j) (param.relabel j) (symbols.relabel j) (types.relabel j) := by
  have hv : (fun i : Fin 6 => (![f,base,g,dest,symbols,types] i).relabel j) =
      ![f.relabel j,base.relabel j,g.relabel j,dest.relabel j,symbols.relabel j,types.relabel j] := by
    funext i
    fin_cases i <;> rfl
  simp only [relation,rhs,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,StructuralExchangeFields.InternalProof.orRename,
    graph2Rename,InternalControlGraphSupportProof.programRename,GuardedSourceSyntaxProof.numeralRename,hv,
    graph2,InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename]

theorem atWitnesses (source target f g base dest node child param symbols types ef eg rf rg value deps vals : OTerm alpha)
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
    (ha : Nonempty (Derivation body Delta (graph2 (InternalListCodec.consCode) vals value z)))
    : Nonempty (Derivation body Delta (relation n arity node f g base dest child param symbols types)) := by
  have hdep := DependenciesProof.singleton n source target f g base dest node child param deps hs ht hn hp hg hd
  have hmap := OriginalDecodedExchangeEquation.StepProof.consValue n arity deps child z param value z vals hd hv
    (OriginalDecodedExchangeEquation.StepProof.nilValue n arity param) ha
  have hans : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) vals node param)) :=
    binaryValue (OriginalDecodedExchangeEquation.answerMap n arity) (OriginalDecodedDependencies.dependencies n) (.projection 1)
      vals deps param ![node,param] hmap hdep (projectionValue 1 ![node,param])
  have hg' := OriginalDecodedLambdaRecurrence.GuardProof.answerTransport n node z vals param hg
  apply andIntro
  · let E := graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hla := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (E :: Delta)
      node param vals (numeral 1) (withHyp hans E)).mp he
    have hc := (ConcreteHeadMoveLayer.OrdinaryProof.internalOrdinary n arity body alpha (E :: Delta)
      (OriginalDecodedLayerCalibration.guard n) node vals param source target f g base dest ef eg rf rg symbols types value z
      (withHyp hg' E) (withHyp hn E) (withHyp hw E) (withHyp hs E) (withHyp ht E)
      (withHyp hef E) (withHyp heg E) (withHyp hrf E) (withHyp hrg E) (withHyp ha E)).mp hla
    have hf := orImp
      (andImp (identityImp (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types])) (EqualityProof.forward OriginalHeadResult.headResult OriginalHeadResult.headResult g f rg rf (withHyp hrg E) (withHyp hrf E)))
      (andImp (EqualityProof.forward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef E) (withHyp heg E))
        (OriginalDecodedBinaryRecurrence.ValuesProof.valueForward n arity child param value (withHyp hv E)))
    obtain ⟨hout⟩ := applyImp hf hc
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let R := rhs n arity f g base dest child param symbols types
    have hh : Nonempty (Derivation body (R :: Delta) R) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := orImp
      (andImp (identityImp (programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types])) (EqualityProof.backward OriginalHeadResult.headResult OriginalHeadResult.headResult g f rg rf (withHyp hrg R) (withHyp hrf R)))
      (andImp (EqualityProof.backward OriginalHeadEncodingBridge.encodeHead OriginalHeadEncodingBridge.encodeHead f g ef eg (withHyp hef R) (withHyp heg R))
        (OriginalDecodedBinaryRecurrence.ValuesProof.valueBackward n arity child param value (withHyp hv R)))
    have hc := applyImp hf hh
    have hla := (ConcreteHeadMoveLayer.OrdinaryProof.internalOrdinary n arity body alpha (R :: Delta)
      (OriginalDecodedLayerCalibration.guard n) node vals param source target f g base dest ef eg rf rg symbols types value z
      (withHyp hg' R) (withHyp hn R) (withHyp hw R) (withHyp hs R) (withHyp ht R)
      (withHyp hef R) (withHyp heg R) (withHyp hrf R) (withHyp hrg R) (withHyp ha R)).mpr hc
    obtain ⟨hout⟩ := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha (R :: Delta)
      node param vals (numeral 1) (withHyp hans R)).mpr hla
    exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.CoreProof
