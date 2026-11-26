module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def count : Program 1 := .composition OriginalContextInsertion.length (fun _ => InternalListCodec.tailCode)
def accumulated : Program 1 := pairOf count (constant 1 0)
def queries : Fin 5 → Program 1 :=
  ![InternalListCodec.headCode,InternalListCodec.tailCode,count,accumulated,LengthWeight.weight]

theorem recover (raw : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![raw]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length (ys 2) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 3) (ys 2) z)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 4) (suc z) z)) := by
  exact ⟨InternalListCodecDecompositionSupportProof.reconstructNonzero raw (ys 0) (ys 1) hn (hq 0) (hq 1),
    unaryRecover OriginalContextInsertion.length InternalListCodec.tailCode (ys 2) (ys 1) ![raw] (hq 2) (hq 1),
    binaryRecover InternalPairing.pairing count (constant 1 0) (ys 3) (ys 2) z ![raw]
      (hq 3) (hq 2) (constantValue 0 ![raw]),
    binaryRecover InternalPairing.pairing (constant 1 1) (constant 1 0) (ys 4) (suc z) z ![raw]
      (hq 4) (constantValue 1 ![raw]) (constantValue 0 ![raw])⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightQueriesProof
