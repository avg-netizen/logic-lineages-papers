module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencySupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryKeyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem boundValue (key code bound param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound))) :
    Nonempty (Derivation body Delta (graph2 (keyBound (.projection 0)) bound key param)) := by
  have hpair := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    key code bound ![code,bound] hk (projectionValue 0 ![code,bound]) (projectionValue 1 ![code,bound])
  have hright := pairOfRight (.projection 0) (.projection 1) key bound ![code,bound]
    hpair (projectionValue 1 ![code,bound])
  exact unaryValue InternalUnpair.right (.projection 0) bound key ![key,param] hright (projectionValue 0 ![key,param])

theorem lambdaDependency (key code bound param domain child childKey listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor code domain child)))
    (hchild : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child (suc bound))))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode childKey z))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode key param)) := by
  have hr := LayerInternalProof.rankAt key code bound param hk
  have ht := lambdaTag (keyRaw (.projection 0)) code domain child ![key,param] hr hc
  have ha := lambdaArity (keyRaw (.projection 0)) code domain child ![key,param] hr hc
  have hf := lambdaFirst (keyRaw (.projection 0)) code domain child ![key,param] hr hc
  have hb := boundValue key code bound param hk
  have hcb : Nonempty (Derivation body Delta (graph2 childBound (suc bound) key param)) := by
    apply branchNumeralIntro 1 1 (leftOf (keyRaw (.projection 0))) _ _ (suc bound) ![key,param] ht
    exact unaryValue .succ (keyBound (.projection 0)) (suc bound) bound ![key,param]
      (successorValue (Fin.cons bound Fin.elim0)) hb
  have hfk := binaryValue InternalPairing.pairing (firstOf (keyRaw (.projection 0))) childBound
    childKey child (suc bound) ![key,param] hchild hf hcb
  exact DependencySupportProof.unaryList key param childKey listCode ha hfk hlist

theorem ordinaryDependency (key code bound param head child childKey listCode : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor code head child)))
    (hchild : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child bound)))
    (hlist : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode childKey z))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode key param)) := by
  have hr := LayerInternalProof.rankAt key code bound param hk
  have ht := ordinaryTag (keyRaw (.projection 0)) code head child ![key,param] hr hc
  have ha := ordinaryArity (keyRaw (.projection 0)) code head child ![key,param] hr hc
  have hf := ordinaryFirst (keyRaw (.projection 0)) code head child ![key,param] hr hc
  have hb := boundValue key code bound param hk
  have hcb : Nonempty (Derivation body Delta (graph2 childBound bound key param)) := by
    apply branchNumeralIntro 4 1 (leftOf (keyRaw (.projection 0))) _ _ bound ![key,param] ht
    exact hb
  have hfk := binaryValue InternalPairing.pairing (firstOf (keyRaw (.projection 0))) childBound
    childKey child bound ![key,param] hchild hf hcb
  exact DependencySupportProof.unaryList key param childKey listCode ha hfk hlist
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryKeyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryKeyProof
