module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransport (constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Fold Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem entry (n : Nat) (entry typ raw bounds : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) bounds raw))) :
    Nonempty (Derivation body Delta (graph1 (entryWeight n) bounds entry)) :=
  unaryValue (OriginalCodeBoundsRecursion.bounds n) InternalUnpair.right bounds raw ![entry]
    hb (pairRight entry typ raw hp)

theorem nil (weight : Program 1) :
    Nonempty (Derivation body Delta (graph1 (weighted weight) z z)) :=
  InternalRawListRecursionProof.nilValue (constant 0 0) (step weight) z Fin.elim0
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 Fin.elim0)

theorem stepValue (weight : Program 1) (entry acc w out : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 weight w entry)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.merge out w acc))) :
    Nonempty (Derivation body Delta (graph2 (step weight) out entry acc)) :=
  binaryValue OriginalBoundsRecombination.merge (.composition weight (fun _ : Fin 1 => .projection 0))
    (.projection 1) out w acc ![entry,acc] hm
    (unaryValue weight (.projection 0) w entry ![entry,acc] hw (projectionValue 0 ![entry,acc]))
    (projectionValue 1 ![entry,acc])

theorem cons (weight : Program 1) (list entry tail acc w out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (ht : Nonempty (Derivation body Delta (graph1 (weighted weight) acc tail)))
    (hw : Nonempty (Derivation body Delta (graph1 weight w entry)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.merge out w acc))) :
    Nonempty (Derivation body Delta (graph1 (weighted weight) out list)) :=
  InternalRawListRecursionProof.consValue (constant 0 0) (step weight) list entry tail acc out Fin.elim0
    hc ht (stepValue weight entry acc w out hw hm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldValueProof
