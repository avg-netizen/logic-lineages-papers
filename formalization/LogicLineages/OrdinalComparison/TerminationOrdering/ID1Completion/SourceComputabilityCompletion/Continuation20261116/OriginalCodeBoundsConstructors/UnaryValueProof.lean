module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.LeafValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalCodeBoundsRecursion
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def constructor (ordinary : Bool) := if ordinary then OriginalRawSyntaxTransport.ordinaryConstructor else OriginalRawSyntaxTransport.lambdaConstructor

theorem rootValue (ordinary : Bool) (n : Nat) (raw metadata child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalBoundsRecombination.root n) (suc (suc z)) raw)) := by
  cases ordinary
  · have ht := lambdaTag (.projection 0) raw metadata child ![raw] (projectionValue 0 ![raw]) hc
    have ht' := unaryRecover InternalUnpair.left (.projection 0) (numeral 1) raw ![raw] ht (projectionValue 0 ![raw])
    exact RootProof.termRoot n 1 (by decide) (by decide) (by decide) raw (suc (suc z)) hg ht'
      InternalApplicationValidityStackAppendTransitionProof.pairOneZero
  · have ht := ordinaryTag (.projection 0) raw metadata child ![raw] (projectionValue 0 ![raw]) hc
    have ht' := unaryRecover InternalUnpair.left (.projection 0) (numeral 4) raw ![raw] ht (projectionValue 0 ![raw])
    exact RootProof.termRoot n 4 (by decide) (by decide) (by decide) raw (suc (suc z)) hg ht'
      InternalApplicationValidityStackAppendTransitionProof.pairOneZero

theorem atLists (ordinary : Bool) (n : Nat) (raw metadata child value size label out deps values : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph1 (bounds n) value child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc size) label)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  have hm := AnswersProof.consMap n deps child z z z value values hd (AnswersProof.nilMap n z)
    (AnswersProof.extractFromBounds n child value he) hv
  have ha := AnswersProof.answersAt n raw z deps values
    (OriginalEnumerationDepth.ChildrenProof.unary ordinary raw z metadata child deps hc hd) hm
  exact ValueProof.fromValues n raw values (suc (suc z)) value out hg ha (rootValue ordinary n raw metadata child hc hg)
    (FoldProof.singleton values value size label hv hp)
    (RootMergeProof.termRoot (suc (suc z)) value size label out
      InternalApplicationValidityStackAppendTransitionProof.pairOneZero hp ho)

theorem value (ordinary : Bool) (n : Nat) (raw metadata child value size label out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph1 (bounds n) value child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value size label)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc size) label))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalEnumerationDepth.ListsProof.unary child value
  intro beta j Theta deps values hj hd hv
  rw [graph1Rename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hej := renameInto he j Theta hj
  have hpj := renameInto hp j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hcj hgj hej hpj hoj
  exact atLists ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j)
    (value.relabel j) (size.relabel j) (label.relabel j) (out.relabel j) deps values hcj hgj hej hpj hoj hd hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
