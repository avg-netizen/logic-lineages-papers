module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AnswersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilMap (n : Nat) (param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) z z param)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) (Equation.answerStep n) z ![param]
    (InternalAcceptanceConjunctionProof.constantZeroValue ![param])

theorem consMap (n : Nat) (code child tail old param value result : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code child tail)))
    (ht : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) old tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value child param)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode result value old))) :
    Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) result code param)) := by
  have hv' := binaryValue (extract n) (.projection 0) (.projection 2)
    value child param ![child,old,param] hv (projectionValue 0 ![child,old,param]) (projectionValue 2 ![child,old,param])
  have hs : Nonempty (Derivation body Delta (graph3 (Equation.answerStep n) result child old param)) :=
    binaryValue InternalListCodec.consCode (.composition (extract n) ![.projection 0,.projection 2]) (.projection 1)
      result value old ![child,old,param] hr hv' (projectionValue 1 ![child,old,param])
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) (Equation.answerStep n)
    code child tail old result ![param] hc ht hs

theorem answersAt (n : Nat) (raw param deps values : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param))) :
    Nonempty (Derivation body Delta (graph2 (Equation.answers n) values raw param)) :=
  binaryValue (Equation.answerMap n) dependency (.projection 1) values deps param ![raw,param]
    hm hd (projectionValue 1 ![raw,param])

theorem fromLayer (n : Nat) (key param values value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (Equation.answers n) values key param)))
    (hl : Nonempty (Derivation body Delta (graph3 (layer n) (InternalTagArithmeticSyntaxProof.suc value) key values param))) :
    Nonempty (Derivation body Delta (graph2 (extract n) value key param)) :=
  (Equation.Proof.exchangeEquation n body alpha Delta key param values value ha).mpr hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AnswersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AnswersProof
