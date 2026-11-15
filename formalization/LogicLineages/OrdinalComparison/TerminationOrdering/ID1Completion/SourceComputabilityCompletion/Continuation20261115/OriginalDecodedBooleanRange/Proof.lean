module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open Continuation20261114
open HeadWindowBooleanRange
open HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atAnswers (n : Nat) (arity : Fin n → Nat) (node answers param out : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) out node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) answers node param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  have hl := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha Delta
    node param answers out ha).mp he
  exact PayloadProof.optionalPayload _ (OriginalDecodedLayerCalibration.guard n) node answers param out hl

theorem exchangeRange (n : Nat) (arity : Fin n → Nat) (node param out : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) out node param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases (OriginalDecodedExchangeEquation.answers n arity)
    (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta answers hj ha
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at ha
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  rw [graph2Rename] at hej
  exact atAnswers n arity (node.relabel j) answers (param.relabel j) (out.relabel j) hej ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Proof
