module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.FieldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph

theorem shapeRename {beta : Type} (s t : OTerm alpha) (j : alpha → beta) :
    (eqn s t ⊓ Targets.active s).relabel j = eqn (s.relabel j) (t.relabel j) ⊓ Targets.active (s.relabel j) := by
  simp only [Targets.active,conjunctionRename,StructuralExchangeFields.InternalProof.orRename,
    eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem atLayer (node source target st sp tt tp answers param : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source st sp)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tt tp)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node answers param)))
    (hl : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node answers param)))
    : Nonempty (Derivation body Delta (eqn st tt ⊓ Targets.active st)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (FieldProof.actualFields n arity)
    (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j xs Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  rw [shapeRename]
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact FieldProof.atFields n arity (node.relabel j) (source.relabel j) (target.relabel j) (st.relabel j) (sp.relabel j) (tt.relabel j) (tp.relabel j) (answers.relabel j) (param.relabel j) xs hnj hsj htj hgj hlj hq

theorem atAnswers (node source target st sp tt tp answers param : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source st sp)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tt tp)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) answers node param)))
    : Nonempty (Derivation body Delta (eqn st tt ⊓ Targets.active st)) := by
  have hg0 := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node param he
  have hg := OriginalDecodedLambdaRecurrence.GuardProof.answerTransport n node z answers param hg0
  have hl := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha Delta
    node param answers (numeral 1) ha).mp he
  exact atLayer n arity node source target st sp tt tp answers param hn hs ht hg hl

theorem successShape (node source target st sp tt tp param : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source st sp)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tt tp)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)))
    : Nonempty (Derivation body Delta (eqn st tt ⊓ Targets.active st)) := by
  apply programCases (OriginalDecodedExchangeEquation.answers n arity) (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta answers hj ha
  simp only [consTermRename,emptyRename] at ha
  rw [shapeRename]
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  exact atAnswers n arity (node.relabel j) (source.relabel j) (target.relabel j) (st.relabel j) (sp.relabel j) (tt.relabel j) (tp.relabel j) answers (param.relabel j) hnj hsj htj hej ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.CoreProof
