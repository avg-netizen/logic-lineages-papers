module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MergeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.FoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (symm addZero)
open Continuation20261115 OriginalBoundsRecombination
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rightZero (value size label : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label))) :
    Nonempty (Derivation body Delta (graph2 merge value value z)) := by
  have ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value
      (OrdinaryArithmetic.addTerm size z) label)) :=
    InternalControlGraphSupportProof.headTransport InternalPairing.pairing value
      size (OrdinaryArithmetic.addTerm size z) (Fin.cons label Fin.elim0) ⟨symm (addZero size)⟩ hp
  exact MergeProof.mergeValue value z size label z z label value hp
    InternalApplicationValidityStackAppendTransitionProof.pairZero
    (OriginalEnumerationDepth.CollectProof.maximumZero label) ho

theorem singleton (code value size label : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code value z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label))) :
    Nonempty (Derivation body Delta (graph1 collect value code)) :=
  MergeProof.collectedCons code value z z value hc
    (OriginalBoundsRecombination.InternalProof.internalNil body alpha Delta) (rightZero value size label hp)

theorem double (code rest left right ls ll rs rl label out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code left rest)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left ls ll)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing right rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (OrdinaryArithmetic.addTerm ls rs) label))) :
    Nonempty (Derivation body Delta (graph1 collect out code)) :=
  MergeProof.collectedCons code left rest right out hc (singleton rest right rs rl hr hp)
    (MergeProof.mergeValue left right ls ll rs rl label out hl hp hm ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.FoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.FoldProof
