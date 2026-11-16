module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CollectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem maximumZero (a : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum a a z)) := by
  have hs := InternalEqualityTestSubtractionSupportProof.subTransport z (InternalAdditionLawsProof.add z a) z a z
    ⟨InternalAdditionLawsProof.leftZero a⟩ ⟨refl z⟩ (InternalEqualityTestSubtractionProof.absorption z a)
  exact zeroBranchIntro InternalLessThan.ltTest (.projection 0) (.projection 1) a ![a,z]
    (InternalLessThanSupportProof.rejectOfZeroDifference a z hs) (projectionValue 0 ![a,z])

theorem nilValue : Nonempty (Derivation body Delta (graph1 collect z z)) :=
  InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 0 0) OriginalBoundsRecombination.maximum
    z Fin.elim0 (constantValue 0 Fin.elim0)

theorem consValue (code head tail result out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hr : Nonempty (Derivation body Delta (graph1 collect result tail)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum out head result))) :
    Nonempty (Derivation body Delta (graph1 collect out code)) :=
  InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 0 0) OriginalBoundsRecombination.maximum
    code head tail result out Fin.elim0 hc hr hm

theorem singleton (code a : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code a z))) :
    Nonempty (Derivation body Delta (graph1 collect a code)) := consValue code a z z a hc nilValue (maximumZero a)

theorem double (code rest a b out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest b z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code a rest)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum out a b))) :
    Nonempty (Derivation body Delta (graph1 collect out code)) := consValue code a rest b out hc (singleton rest b hr) hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CollectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CollectProof
