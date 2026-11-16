module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ZeroMaximumProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm trans congSuc)
open Continuation20261115 OriginalBoundsRecombination
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroRoot (value size label : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label))) :
    Nonempty (Derivation body Delta (graph2 merge value z value)) := by
  have ho := headTransport InternalPairing.pairing value size (OrdinaryArithmetic.addTerm z size)
    (Fin.cons label Fin.elim0) ⟨symm (InternalAdditionLawsProof.leftZero size)⟩ hp
  exact MergeProof.mergeValue z value z z size label label value
    InternalApplicationValidityStackAppendTransitionProof.pairZero hp (ZeroMaximumProof.leftZero label) ho

theorem termRoot (rootValue value size label out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rootValue (suc z) z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label)))
    (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc size) label))) :
    Nonempty (Derivation body Delta (graph2 merge out rootValue value)) := by
  have he : Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn (OrdinaryArithmetic.addTerm (suc z) size) (suc size)) := trans (InternalAdditionLawsProof.leftSuccessor z size)
    (congSuc (InternalAdditionLawsProof.leftZero size))
  have ho := headTransport InternalPairing.pairing out (suc size) (OrdinaryArithmetic.addTerm (suc z) size)
    (Fin.cons label Fin.elim0) ⟨symm he⟩ hout
  exact MergeProof.mergeValue rootValue value (suc z) z size label label out hr hp
    (ZeroMaximumProof.leftZero label) ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
