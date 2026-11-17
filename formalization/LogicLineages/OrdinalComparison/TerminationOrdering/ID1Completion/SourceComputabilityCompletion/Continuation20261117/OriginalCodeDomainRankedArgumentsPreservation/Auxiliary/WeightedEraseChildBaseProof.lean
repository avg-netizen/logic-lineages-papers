module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseChildQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseChildBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalListCodecDecompositionSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open EraseChildQueriesProof (head tail child)
open WeightedEraseChildQueriesProof (queries)

theorem recover (weight : Program 1) (raw needle : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries weight i) (ys i) ![raw,needle]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 Erase.state (ys 2) (ys 1) needle)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 2) (ys 3) (ys 4))) := by
  have hh := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) raw ![raw,needle]
    (hq 0) (projectionValue 0 ![raw,needle])
  have ht := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) raw ![raw,needle]
    (hq 1) (projectionValue 0 ![raw,needle])
  have hc := binaryRecover Erase.state tail (.projection 1) (ys 2) (ys 1) needle ![raw,needle]
    (hq 2) (hq 1) (projectionValue 1 ![raw,needle])
  have hb := unaryRecover InternalUnpair.left child (ys 3) (ys 2) ![raw,needle] (hq 3) (hq 2)
  have hr := unaryRecover InternalUnpair.right child (ys 4) (ys 2) ![raw,needle] (hq 4) (hq 2)
  exact ⟨reconstructNonzero raw (ys 0) (ys 1) hn hh ht,hc,reconstructPair (ys 2) (ys 3) (ys 4) hb hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseChildBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseChildBaseProof
