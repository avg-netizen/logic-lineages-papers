module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SuccessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atAnswers (n : Nat) (arity : Fin n → Nat) (node param values : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answers n arity) values node param)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))) :
    Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)) := by
  have hg := (OriginalDecodedExchangeEquation.Proof.exchangeEquation n arity body alpha Delta node param values (numeral 1) ha).mp he
  exact GuardProof.answerTransport n node values z param (AcceptanceProof.layerGuard n arity node values param hg)

theorem guardNecessary (n : Nat) (arity : Fin n → Nat) (node param : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param))) :
    Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param)) := by
  apply programCases (OriginalDecodedExchangeEquation.answers n arity) (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta values hj ha
  simp only [consTermRename,emptyRename] at ha
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename,zRelabel]
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  exact atAnswers n arity (node.relabel j) (param.relabel j) values ha hej
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SuccessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SuccessProof
