module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryInputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem answers (n : Nat) (key param leftKey rightKey depRest deps leftOut rightOut valueRest values : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hl : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hr : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest))) :
    Nonempty (Derivation body Delta (graph2 (Equation.answers n) values key param)) :=
  AnswersProof.answersAt n key param deps values hd
    (AnswersProof.consMap n deps leftKey depRest valueRest param leftOut values hc
      (AnswersProof.consMap n depRest rightKey z z param rightOut valueRest ht (AnswersProof.nilMap n param) hr hvr) hl hvs)

theorem secondValue (key param values leftOut valueRest rightOut tail : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut tail))) :
    Nonempty (Derivation body Delta (graph3 secondAnswer rightOut key values param)) := by
  have ht := InternalRawListRecursionSupportProof.consTail values leftOut valueRest hl
  have hh := InternalRawListRecursionSupportProof.consHead valueRest rightOut tail hr
  have htg := LayerGuardProof.unaryVectorValue InternalListCodec.tailCode (.projection 1) valueRest values ![key,values,param]
    ht (projectionValue 1 ![key,values,param])
  exact LayerGuardProof.unaryVectorValue InternalListCodec.headCode
    (.composition InternalListCodec.tailCode ![.projection 1]) rightOut valueRest ![key,values,param] hh htg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryInputProof
