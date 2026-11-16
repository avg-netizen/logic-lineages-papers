module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.FirstRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SecondRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.LayerPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SelectorRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open Continuation20261114.HeadWindowBooleanRange
open PointRange PointBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat) (key param deps parentRank values first rest second : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (hf : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode first values)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode rest values)))
    (hs : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode second rest))) :
    Nonempty (Derivation body Delta (At (LayerInternalProof.payload n) ![key,values,param])) := by
  have hfirst := FirstRangeProof.headRange n key param deps parentRank values first ih hp hd hm hf
  have hsecond := SecondRangeProof.secondRange n key param deps parentRank values rest second ih hp hd hm ht hs
  have hfg := LayerGuardProof.unaryVectorValue InternalListCodec.headCode (.projection 1) first values ![key,values,param]
    hf (projectionValue 1 ![key,values,param])
  have htg := LayerGuardProof.unaryVectorValue InternalListCodec.tailCode (.projection 1) rest values ![key,values,param]
    ht (projectionValue 1 ![key,values,param])
  have hsg := LayerGuardProof.unaryVectorValue InternalListCodec.headCode
    (.composition InternalListCodec.tailCode ![.projection 1]) second rest ![key,values,param] hs htg
  exact LayerPointProof.payloadAt n ![key,values,param]
    (fromValue firstAnswer ![key,values,param] first hfg hfirst)
    (fromValue secondAnswer ![key,values,param] second hsg hsecond)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SelectorRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SelectorRangeProof
