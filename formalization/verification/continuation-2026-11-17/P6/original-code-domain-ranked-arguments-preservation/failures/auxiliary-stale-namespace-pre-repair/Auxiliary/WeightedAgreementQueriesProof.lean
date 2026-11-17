module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementConsAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z eqn)
def head : Program 2 := .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 0)
def tail : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0)
def erased : Program 2 := .composition Erase.state ![.projection 1,head]
def tailFold (weight : Program 1) : Program 2 := .composition (Fold.weighted weight) (fun _ : Fin 1 => tail)
def restFold (weight : Program 1) : Program 2 := .composition (Fold.weighted weight) (fun _ : Fin 1 => rightOf erased)
def headWeight (weight : Program 1) : Program 2 := .composition weight (fun _ : Fin 1 => head)
def queries (weight : Program 1) : Fin 8 → Program 2 :=
  ![head,tail,erased,leftOf erased,rightOf erased,tailFold weight,restFold weight,headWeight weight]

theorem recover (weight : Program 1) (left right : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn left z).not))
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries weight i) (ys i) ![left,right]))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left (ys 0) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph2 Erase.state (ys 2) right (ys 0))) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 2) (ys 3) (ys 4))) ∧
    Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) (ys 5) (ys 1))) ∧
    Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) (ys 6) (ys 4))) ∧
    Nonempty (Derivation body Delta (graph1 weight (ys 7) (ys 0))) := by
  have hh := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) left ![left,right]
    (hq 0) (projectionValue 0 ![left,right])
  have ht := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) left ![left,right]
    (hq 1) (projectionValue 0 ![left,right])
  have he := binaryRecover Erase.state (.projection 1) head (ys 2) right (ys 0) ![left,right]
    (hq 2) (projectionValue 1 ![left,right]) (hq 0)
  have hb := unaryRecover InternalUnpair.left erased (ys 3) (ys 2) ![left,right] (hq 3) (hq 2)
  have hr := unaryRecover InternalUnpair.right erased (ys 4) (ys 2) ![left,right] (hq 4) (hq 2)
  exact ⟨InternalListCodecDecompositionSupportProof.reconstructNonzero left (ys 0) (ys 1) hn hh ht,
    he,reconstructPair (ys 2) (ys 3) (ys 4) hb hr,
    unaryRecover (Fold.weighted weight) tail (ys 5) (ys 1) ![left,right] (hq 5) (hq 1),
    unaryRecover (Fold.weighted weight) (rightOf erased) (ys 6) (ys 4) ![left,right] (hq 6) (hq 4),
    unaryRecover weight head (ys 7) (ys 0) ![left,right] (hq 7) (hq 0)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementQueriesProof
