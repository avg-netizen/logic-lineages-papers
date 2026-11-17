module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem mergeValue (left right ls ll rs rl label out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing left ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing right rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out
      (OrdinaryArithmetic.addTerm ls rs) label))) :
    Nonempty (Derivation body Delta (graph2 merge out left right)) := by
  let xs : Fin 2 → OTerm alpha := ![left,right]
  have hls := unaryValue InternalUnpair.left (.projection 0) ls left xs (pairLeft left ls ll hl) (projectionValue 0 xs)
  have hll := unaryValue InternalUnpair.right (.projection 0) ll left xs (pairRight left ls ll hl) (projectionValue 0 xs)
  have hrs := unaryValue InternalUnpair.left (.projection 1) rs right xs (pairLeft right rs rl hr) (projectionValue 1 xs)
  have hrl := unaryValue InternalUnpair.right (.projection 1) rl right xs (pairRight right rs rl hr) (projectionValue 1 xs)
  have ha := binaryValue InternalArithmeticPrograms.addition (leftOf (.projection 0)) (leftOf (.projection 1))
    (OrdinaryArithmetic.addTerm ls rs) ls rs xs (InternalArithmeticProgramsSupportProof.additionValue ls rs) hls hrs
  have hb := binaryValue maximum (rightOf (.projection 0)) (rightOf (.projection 1)) label ll rl xs hm hll hrl
  exact binaryValue InternalPairing.pairing
    (addOf (leftOf (.projection 0)) (leftOf (.projection 1)))
    (.composition maximum ![rightOf (.projection 0),rightOf (.projection 1)]) out
    (OrdinaryArithmetic.addTerm ls rs) label xs ho ha hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeBaseProof
