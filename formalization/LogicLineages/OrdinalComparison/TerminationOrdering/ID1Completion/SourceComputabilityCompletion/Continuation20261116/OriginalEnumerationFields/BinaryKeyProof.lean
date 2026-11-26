module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryKeyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryKeyProof
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

theorem applicationDependency (key code bound param typ left right leftKey rightKey rest deps : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor code typ left right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left bound)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right bound)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest rightKey z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey rest))) :
    Nonempty (Derivation body Delta (graph2 dependency deps key param)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have htag := applicationTag (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have ha := applicationArity (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hf := applicationFirst (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hs := applicationSecond (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hb := UnaryKeyProof.boundValue key code bound param hk
  have hcb : Nonempty (Derivation body Delta (graph2 childBound bound key param)) :=
    branchNumeralIntro 2 1 (leftOf (keyRaw (.projection 0))) _ _ bound ![key,param] htag hb
  have hfk := binaryValue InternalPairing.pairing (firstOf (keyRaw (.projection 0))) childBound
    leftKey left bound ![key,param] hl hf hcb
  have hsk := binaryValue InternalPairing.pairing (secondOf (keyRaw (.projection 0))) (keyBound (.projection 0))
    rightKey right bound ![key,param] hr hs hb
  exact DependencySupportProof.binaryList key param leftKey rightKey rest deps ha hfk hsk ht hd

theorem consDependency (key code bound param typ left right leftKey rightKey rest deps : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor code typ left right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left bound)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right bound)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest rightKey z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey rest))) :
    Nonempty (Derivation body Delta (graph2 dependency deps key param)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have htag := consTag (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have ha := consArity (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hf := consFirst (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hs := consSecond (keyRaw (.projection 0)) code typ left right ![key,param] hraw hc
  have hb := UnaryKeyProof.boundValue key code bound param hk
  have hcb : Nonempty (Derivation body Delta (graph2 childBound bound key param)) :=
    branchNumeralIntro 7 1 (leftOf (keyRaw (.projection 0))) _ _ bound ![key,param] htag hb
  have hfk := binaryValue InternalPairing.pairing (firstOf (keyRaw (.projection 0))) childBound
    leftKey left bound ![key,param] hl hf hcb
  have hsk := binaryValue InternalPairing.pairing (secondOf (keyRaw (.projection 0))) (keyBound (.projection 0))
    rightKey right bound ![key,param] hr hs hb
  exact DependencySupportProof.binaryList key param leftKey rightKey rest deps ha hfk hsk ht hd

theorem numberedDependency (key code bound param label head typ base types extra leftKey rightKey rest deps : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor code ![label,head,typ,base,types,extra])))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey base bound)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey extra bound)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest rightKey z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey rest))) :
    Nonempty (Derivation body Delta (graph2 dependency deps key param)) := by
  have hraw := LayerInternalProof.rankAt key code bound param hk
  have htag := numberedTag (keyRaw (.projection 0)) code label head typ base types extra ![key,param] hraw hc
  have ha := numberedArity (keyRaw (.projection 0)) code label head typ base types extra ![key,param] hraw hc
  have hf := numberedFirst (keyRaw (.projection 0)) code label head typ base types extra ![key,param] hraw hc
  have hs := numberedSecond (keyRaw (.projection 0)) code label head typ base types extra ![key,param] hraw hc
  have hb := UnaryKeyProof.boundValue key code bound param hk
  have hcb : Nonempty (Derivation body Delta (graph2 childBound bound key param)) :=
    branchNumeralIntro 5 1 (leftOf (keyRaw (.projection 0))) _ _ bound ![key,param] htag hb
  have hfk := binaryValue InternalPairing.pairing (firstOf (keyRaw (.projection 0))) childBound
    leftKey base bound ![key,param] hl hf hcb
  have hsk := binaryValue InternalPairing.pairing (secondOf (keyRaw (.projection 0))) (keyBound (.projection 0))
    rightKey extra bound ![key,param] hr hs hb
  exact DependencySupportProof.binaryList key param leftKey rightKey rest deps ha hfk hsk ht hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryKeyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryKeyProof
