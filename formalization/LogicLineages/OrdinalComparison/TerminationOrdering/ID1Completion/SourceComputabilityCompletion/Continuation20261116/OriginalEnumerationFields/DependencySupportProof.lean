module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencySupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def singleton : Program 2 := consOf firstKey (constant 2 0)
def double : Program 2 := consOf firstKey (consOf secondKey (constant 2 0))

theorem zeroList (key param : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (arityOf (keyRaw (.projection 0))) z key param))) :
    Nonempty (Derivation body Delta (graph2 dependency z key param)) :=
  zeroBranchIntro _ _ _ z ![key,param] ha (constantValue 0 ![key,param])

theorem unaryList (key param child listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (arityOf (keyRaw (.projection 0))) (numeral 1) key param)))
    (hf : Nonempty (Derivation body Delta (graph2 firstKey child key param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode child z))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode key param)) := by
  apply successorBranchIntro (arityOf (keyRaw (.projection 0))) (constant 2 0) _ listCode z ![key,param] ha
  apply branchNumeralIntro 1 2 (arityOf (keyRaw (.projection 0))) singleton double listCode ![key,param] ha
  exact binaryValue InternalListCodec.consCode firstKey (constant 2 0) listCode child z ![key,param]
    hc hf (constantValue 0 ![key,param])

theorem binaryList (key param left right rest listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (arityOf (keyRaw (.projection 0))) (numeral 2) key param)))
    (hf : Nonempty (Derivation body Delta (graph2 firstKey left key param)))
    (hs : Nonempty (Derivation body Delta (graph2 secondKey right key param)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode left rest))) :
    Nonempty (Derivation body Delta (graph2 dependency listCode key param)) := by
  apply successorBranchIntro (arityOf (keyRaw (.projection 0))) (constant 2 0) _ listCode (numeral 1) ![key,param] ha
  apply branchNumeralIntro 2 2 (arityOf (keyRaw (.projection 0))) singleton double listCode ![key,param] ha
  have hrest := binaryValue InternalListCodec.consCode secondKey (constant 2 0) rest right z ![key,param]
    hr hs (constantValue 0 ![key,param])
  exact binaryValue InternalListCodec.consCode firstKey (consOf secondKey (constant 2 0)) listCode left rest ![key,param]
    hc hf hrest

theorem firstRank (key code bound param child first : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hchild : Nonempty (Derivation body Delta (graph2 firstKey child key param)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first code))) :
    Nonempty (Derivation body Delta (graph2 rank first child param)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have hfirst := SelectorTransferProof.firstAt (keyRaw (.projection 0)) ![key,param] code first hraw hf
  have hleft := pairOfLeft (firstOf (keyRaw (.projection 0))) childBound child first ![key,param] hchild hfirst
  exact unaryValue InternalUnpair.left (.projection 0) first child ![child,param] hleft (projectionValue 0 ![child,param])

theorem secondRank (key code bound param child second : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hchild : Nonempty (Derivation body Delta (graph2 secondKey child key param)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second code))) :
    Nonempty (Derivation body Delta (graph2 rank second child param)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have hsecond := SelectorTransferProof.secondAt (keyRaw (.projection 0)) ![key,param] code second hraw hs
  have hleft := pairOfLeft (secondOf (keyRaw (.projection 0))) (keyBound (.projection 0)) child second ![key,param] hchild hsecond
  exact unaryValue InternalUnpair.left (.projection 0) second child ![child,param] hleft (projectionValue 0 ![child,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencySupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencySupportProof
