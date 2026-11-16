module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinarySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryForwardProof
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

theorem atPair (n : Nat) (heads prior code converted pairs payload raw base : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pairs payload)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload raw base)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload 4) code payload))) :
    Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code)) := by
  have hmembers := NumericDependencyCross.CrossProof.projection converted prior pairs payload raw base hp hm hq
  have himage := MapElimProof.recover (OriginalEncodedHeadConversion.convert n) heads converted raw hc (andLeft hmembers)
  have hctor := TagProof.introduce 4 TagProof.binaryPayload ![raw,base] code payload (TagProof.binaryAt raw base payload hq) ht
  have hbase := andRight hmembers
  apply MapImageEliminationProof.cases (OriginalEncodedHeadConversion.convert n) heads raw _ himage
  intro beta j Theta encoded hj hmem hconvert
  rw [OrdinarySyntaxProof.caseRename]
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hbase j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hbj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto hctor j Theta hj
  rw [programRename] at htj
  exact OrdinarySyntaxProof.introduce n (heads.relabel j) (prior.relabel j) (code.relabel j)
    ![encoded,raw.relabel j,base.relabel j] (andIntro (andIntro (andIntro hmem hconvert) hbj) htj)

theorem atPayload (n : Nat) (heads prior code converted pairs payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pairs payload)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload 4) code payload))) :
    Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code)) := by
  apply OriginalDecodedRank.SupportProof.pairCases payload _
  intro beta j Theta raw base hj hq
  rw [OrdinarySyntaxProof.caseRename]
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph1Rename] at htj
  exact atPair n (heads.relabel j) (prior.relabel j) (code.relabel j)
    (converted.relabel j) (pairs.relabel j) (payload.relabel j) raw base hcj hpj hmj hq htj

theorem atMap (n : Nat) (heads prior out code converted pairs : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4)) out pairs)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code)) := by
  have hi := MapElimProof.recover (OriginalEnumerationConstructorLayer.tagPayload 4) pairs out code hg hm
  apply MapImageEliminationProof.cases (OriginalEnumerationConstructorLayer.tagPayload 4) pairs code _ hi
  intro beta j Theta payload hj hmem htag
  rw [OrdinarySyntaxProof.caseRename]
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  exact atPayload n (heads.relabel j) (prior.relabel j) (code.relabel j)
    (converted.relabel j) (pairs.relabel j) payload hcj hpj hmem htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryForwardProof
