module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.LeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem payloadValue (tag : Nat) (raw out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral tag) raw))) :
    Nonempty (Derivation body Delta (graph1 (payloadHead tag) out raw)) :=
  binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 tag) (.projection 0)
    out (numeral tag) raw ![raw] h (constantValue tag ![raw]) (projectionValue 0 ![raw])

theorem booleanZero (out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z z))) :
    Nonempty (Derivation body Delta (graph1 booleanHead out z)) := by
  have hn : Nonempty (Derivation body Delta (eqn (z : OTerm alpha) (suc z)).not) :=
    ⟨Derivation.implicationIntroduction (zeroNeSuc (Derivation.hypothesis List.mem_cons_self))⟩
  have he := OriginalVariableDecoderEqualityProof.equalityReject z (suc z) hn
  have hg := binaryValue InternalEqualityTest.equalityTest (.projection 0)
    (OriginalRawSyntaxTransport.constant 1 1) z z (suc z) ![z] he
    (projectionValue 0 ![z]) (constantValue 1 ![z])
  have hzero := zeroBranchIntro (OriginalRawSyntaxTransport.sameOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 1))
    (OriginalRawSyntaxTransport.constant 1 0)
    (pairOf (OriginalRawSyntaxTransport.constant 1 1) (OriginalRawSyntaxTransport.constant 1 0)) z ![z] hg (constantValue 0 ![z])
  have heq := valueUnique InternalPairing.pairing z out ![z,z]
    InternalApplicationValidityStackAppendTransitionProof.pairZero hp
  exact outputTransport booleanHead z out ![z] heq hzero

theorem booleanOne (out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) z))) :
    Nonempty (Derivation body Delta (graph1 booleanHead out (suc z))) := by
  have he := InternalEqualityTestCompositionProof.equalityOfEqual (suc (z : OTerm alpha)) (suc z)
    (body := body) (Gamma := Delta) ⟨refl _⟩
  have hg := binaryValue InternalEqualityTest.equalityTest (.projection 0)
    (OriginalRawSyntaxTransport.constant 1 1) (suc z) (suc z) (suc z) ![suc z] he
    (projectionValue 0 ![suc z]) (constantValue 1 ![suc z])
  have hv := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 1)
    (OriginalRawSyntaxTransport.constant 1 0) out (suc z) z ![suc z] hp
    (constantValue 1 ![suc z]) (constantValue 0 ![suc z])
  exact successorBranchIntro (OriginalRawSyntaxTransport.sameOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 1))
    (OriginalRawSyntaxTransport.constant 1 0)
    (pairOf (OriginalRawSyntaxTransport.constant 1 1) (OriginalRawSyntaxTransport.constant 1 0))
    out z ![suc z] hg hv

theorem rankedValue (n : Nat) (raw out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (numeral 5) raw)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (numeral n)))) :
    Nonempty (Derivation body Delta (graph1 (rankedHead n) out raw)) := by
  have hl := InternalLessThanSupportProof.acceptOfLess raw (numeral n) hb
  have hg := binaryValue InternalLessThan.ltTest (.projection 0) (OriginalRawSyntaxTransport.constant 1 n)
    (suc z) raw (numeral n) ![raw] hl (projectionValue 0 ![raw]) (constantValue n ![raw])
  exact successorBranchIntro (.composition InternalLessThan.ltTest ![.projection 0,OriginalRawSyntaxTransport.constant 1 n])
    (OriginalRawSyntaxTransport.constant 1 0) (payloadHead 5) out z ![raw] hg (payloadValue 5 raw out hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.LeafProof
