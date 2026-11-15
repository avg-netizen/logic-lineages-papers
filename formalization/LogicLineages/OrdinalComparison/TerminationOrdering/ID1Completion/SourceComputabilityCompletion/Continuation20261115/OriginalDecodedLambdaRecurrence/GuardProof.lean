module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalDecodedLayerCalibration
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nodeRecover (n : Nat) (node answers param : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node answers param))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.accepted n) (numeral 1) node param)) := by
  have hc := conjunctionRecover (nodeAccepted n) (windowAccepted n) ![node,answers,param] h
  exact binaryRecover (OriginalDecodedDependencies.accepted n) (.projection 0) (.projection 2)
    (numeral 1) node param ![node,answers,param] (andLeft hc)
    (projectionValue 0 ![node,answers,param]) (projectionValue 2 ![node,answers,param])

theorem windowRecover (n : Nat) (node answers param : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node answers param))) :
    Nonempty (Derivation body Delta (graph1 (OriginalDecodedWindowValidity.window n) (numeral 1) param)) := by
  have hc := conjunctionRecover (nodeAccepted n) (windowAccepted n) ![node,answers,param] h
  exact unaryRecover (OriginalDecodedWindowValidity.window n) (.projection 2)
    (numeral 1) param ![node,answers,param] (andRight hc) (projectionValue 2 ![node,answers,param])

theorem introduce (n : Nat) (node answers param : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.accepted n) (numeral 1) node param)))
    (hw : Nonempty (Derivation body Delta (graph1 (OriginalDecodedWindowValidity.window n) (numeral 1) param))) :
    Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node answers param)) :=
  conjunctionAccept (nodeAccepted n) (windowAccepted n) ![node,answers,param]
    (binaryValue (OriginalDecodedDependencies.accepted n) (.projection 0) (.projection 2)
      (numeral 1) node param ![node,answers,param] hn (projectionValue 0 ![node,answers,param]) (projectionValue 2 ![node,answers,param]))
    (unaryValue (OriginalDecodedWindowValidity.window n) (.projection 2)
      (numeral 1) param ![node,answers,param] hw (projectionValue 2 ![node,answers,param]))

theorem answerTransport (n : Nat) (node first second param : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node first param))) :
    Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node second param)) :=
  introduce n node second param (nodeRecover n node first param h) (windowRecover n node first param h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
