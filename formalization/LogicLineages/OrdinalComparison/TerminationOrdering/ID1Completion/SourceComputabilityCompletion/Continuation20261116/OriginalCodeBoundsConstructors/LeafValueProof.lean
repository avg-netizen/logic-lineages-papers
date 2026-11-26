module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.FoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.LeafValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open Continuation20261115 OriginalCodeBoundsRecursion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leaf (n : Nat) (raw out size label : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency z raw z)))
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalBoundsRecombination.root n) out raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out size label))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) :=
  ValueProof.fromValues n raw z out z out hg
    (AnswersProof.answersAt n raw z z z hd (AnswersProof.nilMap n z)) hr
    (OriginalBoundsRecombination.InternalProof.internalNil body alpha Delta)
    (FoldProof.rightZero out size label hp)

theorem variableValue (n : Nat) (raw index out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) z))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) :=
  leaf n raw out (suc z) z hg (OriginalEnumerationDepth.ChildrenProof.variableLeaf raw z index hc)
    (RootProof.termRoot n 0 (by decide) (by decide) (by decide) raw out hg
      (pairLeft raw (numeral 0) index (variableConstructorPair raw index hc)) hp) hp

theorem bottomValue (n : Nat) (raw typ out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw typ)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) z))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) :=
  leaf n raw out (suc z) z hg (OriginalEnumerationDepth.ChildrenProof.bottom raw z typ hc)
    (RootProof.termRoot n 3 (by decide) (by decide) (by decide) raw out hg
      (pairLeft raw (numeral 3) typ (bottomConstructorPair raw typ hc)) hp) hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.LeafValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.LeafValueProof
