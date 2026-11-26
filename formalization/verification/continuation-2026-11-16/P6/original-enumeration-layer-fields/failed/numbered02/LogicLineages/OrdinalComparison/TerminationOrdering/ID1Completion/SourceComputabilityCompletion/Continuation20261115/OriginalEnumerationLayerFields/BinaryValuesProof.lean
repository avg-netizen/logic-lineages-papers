module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinarySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def constructor (tag : Nat) : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 tag) TagProof.ternaryPayload

theorem fieldsFromPairs (tag : Nat) (types prior code pairs children payload inner t q a : OTerm alpha)
    (hcross : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hchildren : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hmem : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pairs payload)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload t inner)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner q a)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload tag) code payload))) :
    Nonempty (Derivation body Delta (BinarySyntaxProof.fields (constructor tag) types prior code t q a)) := by
  have outer := NumericDependencyCross.CrossProof.projection types children pairs payload t inner hcross hmem hp
  have child := NumericDependencyCross.CrossProof.projection prior prior children inner q a hchildren (andRight outer) hi
  have ctor := TagProof.introduce tag TagProof.ternaryPayload ![t,q,a] code payload
    (TagProof.ternaryAt t q a inner payload hi hp) ht
  exact andIntro (andIntro (andIntro (andLeft outer) (andLeft child)) (andRight child)) ctor

theorem memberFromFields (tag : Nat) (types prior out code pairs children payload inner t q a : OTerm alpha)
    (hmap : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag)) out pairs)))
    (hcross : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hchildren : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload t inner)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner q a)))
    (hf : Nonempty (Derivation body Delta (BinarySyntaxProof.fields (constructor tag) types prior code t q a))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have child := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce prior prior children inner q a hchildren
    (andIntro (andRight (andLeft (andLeft hf))) (andRight (andLeft hf))) hi
  have outer := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce types children pairs payload t inner hcross
    (andIntro (andLeft (andLeft (andLeft hf))) child) hp
  have ht := TagProof.recover tag TagProof.ternaryPayload ![t,q,a] code payload
    (TagProof.ternaryAt t q a inner payload hi hp) (andRight hf)
  exact MapIntroProof.introduce (OriginalEnumerationConstructorLayer.tagPayload tag) pairs z out code z payload hmap outer ht

theorem childrenAt (xs : Fin 7 → OTerm alpha) (children : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.childPairs children xs))) :
    Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children (xs 5) (xs 5))) :=
  binaryRecover NumericDependencyCross.cross (.projection 5) (.projection 5) children (xs 5) (xs 5) xs hp
    (projectionValue 5 xs) (projectionValue 5 xs)

theorem pairsAt (xs : Fin 7 → OTerm alpha) (pairs children : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.typedChildPairs pairs xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.childPairs children xs))) :
    Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs (xs 0) children)) :=
  binaryRecover NumericDependencyCross.cross (.projection 0) OriginalEnumerationConstructorLayer.childPairs
    pairs (xs 0) children xs hp (projectionValue 0 xs) hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryValuesProof
