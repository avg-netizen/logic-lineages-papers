module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LengthWeight Auxiliary
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem weightValue (entry value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value (suc z) z))) :
    Nonempty (Derivation body Delta (graph1 weight value entry)) :=
  binaryValue InternalPairing.pairing (constant 1 1) (constant 1 0) value (suc z) z ![entry]
    hp (constantValue 1 ![entry]) (constantValue 0 ![entry])

theorem maximumZero : Nonempty (Derivation body Delta
    (graph2 BoundsRecombination.maximum (z : OTerm alpha) z z)) :=
  InternalAcceptanceBranchProof.zeroBranchIntro InternalLessThan.ltTest (.projection 0)
    (.projection 1) z ![z,z]
    (InternalLessThanSupportProof.rejectOfEqual z z ⟨refl z⟩) (projectionValue 0 ![z,z])

theorem mergeCount (count acc one out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc count z)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing one (suc z) z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc count) z))) :
    Nonempty (Derivation body Delta (graph2 BoundsRecombination.merge out one acc)) := by
  have he : Nonempty (Derivation body Delta (eqn (suc count) (OrdinaryArithmetic.addTerm (suc z) count))) :=
    ⟨symm (trans (InternalAdditionLawsProof.leftSuccessor z count)
      (congSuc (InternalAdditionLawsProof.leftZero count)))⟩
  exact MergeBaseProof.mergeValue one acc (suc z) z count z z out hw ha maximumZero
    (headTransport InternalPairing.pairing out (suc count) (OrdinaryArithmetic.addTerm (suc z) count)
      ![z] he ho)

theorem consValue (list entry tail count acc one out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (hf : Nonempty (Derivation body Delta (result tail acc)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc count z)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing one (suc z) z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc count) z))) :
    Nonempty (Derivation body Delta (result list out)) :=
  FoldValueProof.cons weight list entry tail acc one out hc hf (weightValue entry one hw)
    (mergeCount count acc one out ha hw ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightValueProof
