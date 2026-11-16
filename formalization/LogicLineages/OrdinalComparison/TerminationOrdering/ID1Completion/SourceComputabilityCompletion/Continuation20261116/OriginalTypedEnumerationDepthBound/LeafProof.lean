module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem variableCode (n : Nat) (raw field pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw field)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (termBound depth size ⊓ InternalLessThan.strictLess z size)) := by
  have hcanonical := InternalApplicationValidityStackAppendTransitionProof.pairOneZero
    (body := body) (Gamma := Delta) (α := alpha)
  have hv := OriginalCodeBoundsConstructors.LeafValueProof.variableValue n raw field (suc (suc z)) hc hg hcanonical
  have hs := LeafMeasureProof.measuredSize n raw pair size label (suc (suc z)) (suc z) z hb hp hv hcanonical
  have he := LeafMeasureProof.measuredDepth n raw depth hg hd
    (OriginalEnumerationDepth.ChildrenProof.variableLeaf raw z field hc)
  exact LeafMeasureProof.termResult size depth hs he

theorem bottom (n : Nat) (raw field pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw field)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (termBound depth size ⊓ InternalLessThan.strictLess z size)) := by
  have hcanonical := InternalApplicationValidityStackAppendTransitionProof.pairOneZero
    (body := body) (Gamma := Delta) (α := alpha)
  have hv := OriginalCodeBoundsConstructors.LeafValueProof.bottomValue n raw field (suc (suc z)) hc hg hcanonical
  have hs := LeafMeasureProof.measuredSize n raw pair size label (suc (suc z)) (suc z) z hb hp hv hcanonical
  have he := LeafMeasureProof.measuredDepth n raw depth hg hd
    (OriginalEnumerationDepth.ChildrenProof.bottom raw z field hc)
  exact LeafMeasureProof.termResult size depth hs he

theorem nilCode (n : Nat) (raw pair size label depth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))) :
    Nonempty (Derivation body Delta (argumentsBound depth size)) := by
  have hv := OriginalCodeBoundsConstructors.NilValueProof.nilValue n raw hc hg
  have hs := LeafMeasureProof.measuredSize n raw pair size label z z z hb hp hv
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  have he := LeafMeasureProof.measuredDepth n raw depth hg hd
    (OriginalEnumerationDepth.ChildrenProof.nil raw z hc)
  exact LeafMeasureProof.argumentsResult size depth hs he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafProof
