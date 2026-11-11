module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof
open OriginalRawSyntaxTransportInternalCancellationProof
open OriginalRawSyntaxTransportInternalCancellationBindingProof
open OriginalRawSyntaxTransportInternalInterfaceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- This genuinely internal right inverse comes from the accepted original
all-raw induction supplier. No standard-model reflection is involved. -/
theorem rawRightInverse (raw shifted d k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted k raw))) :
    Nonempty (Derivation body Delta (graph3 eraseRaw raw d k shifted)) :=
  atRawApply (fold .shift) (fold .erase) raw d k shifted (allRawCancellation raw)
    (zeroFirstForward (fold .shift) shifted k raw hs)

theorem packedRightInverseAt (packed shifted tau raw shiftedRaw d k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (hr : Nonempty (Derivation body Delta (graph2 shiftRaw shiftedRaw k raw)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed))) :
    Nonempty (Derivation body Delta (graph3 erasePackedRaw packed d k shifted)) := by
  have hp' := shiftPackedForward packed shifted tau raw shiftedRaw k hp hr hs
  exact erasePackedBackward shifted packed tau shiftedRaw raw d k hp'
    (rawRightInverse raw shiftedRaw d k hr) hp

/-- These queries expose the literal packed type and code, without requiring
a typed source term or a decoding premise. Inputs are [packed,cutoff]. -/
def packedQueries : Fin 3 → Program 2 :=
  ![leftOf (.projection 0),rightOf (.projection 0),
    .composition shiftRaw ![.projection 1,rightOf (.projection 0)] ]

theorem packedRightInverse (packed shifted d k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed))) :
    Nonempty (Derivation body Delta (graph3 erasePackedRaw packed d k shifted)) := by
  apply queryCases packedQueries (Fin.cons packed (Fin.cons k Fin.elim0)) _
  intro beta j ys Theta hj hq
  rw [graph3Rename]
  let xs : Fin 2 → OTerm beta := Fin.cons (packed.relabel j) (Fin.cons (k.relabel j) Fin.elim0)
  have hq' : ∀ i, Nonempty (Derivation body Theta
      (programGraph (packedQueries i) (ys i) xs)) :=
    fun i => queryTwoRename (packedQueries i) packed k j Theta (ys i) (hq i)
  have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (packed.relabel j) xs
    (hq' 0) (projectionValue 0 xs)
  have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (packed.relabel j) xs
    (hq' 1) (projectionValue 0 xs)
  have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) hl hr
  have ht := binaryRecover shiftRaw (.projection 1) (rightOf (.projection 0))
    (ys 2) (k.relabel j) (ys 1) xs (hq' 2) (projectionValue 1 xs) (hq' 1)
  have hs' := binaryRename shiftPackedRaw shifted k packed hs j Theta hj
  exact packedRightInverseAt (packed.relabel j) (shifted.relabel j) (ys 0) (ys 1) (ys 2)
    (d.relabel j) (k.relabel j) hp ht hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
