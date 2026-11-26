module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryValuesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryForwardProof
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

theorem atPayload (tag : Nat) (types prior code pairs children payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hc : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pairs payload)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationConstructorLayer.tagPayload tag) code payload))) :
    Nonempty (Derivation body Delta (Targets.typedBinaryCase (BinaryValuesProof.constructor tag) types prior code)) := by
  apply OriginalDecodedRank.SupportProof.pairCases payload _
  intro beta j Theta t inner hj hpair
  rw [BinarySyntaxProof.caseRename]
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  rw [graph1Rename] at htj
  apply OriginalDecodedRank.SupportProof.pairCases inner _
  intro gamma k Xi q a hk hinner
  rw [BinarySyntaxProof.caseRename]
  have hpk := InternalGraphCompositionFunctionalityProof.renameInto hpj k Xi hk
  rw [graph2Rename] at hpk
  have hck := InternalGraphCompositionFunctionalityProof.renameInto hcj k Xi hk
  rw [graph2Rename] at hck
  have hmk := InternalGraphCompositionFunctionalityProof.renameInto hmj k Xi hk
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmk
  have htk := InternalGraphCompositionFunctionalityProof.renameInto htj k Xi hk
  rw [graph1Rename] at htk
  have hpairk := InternalGraphCompositionFunctionalityProof.renameInto hpair k Xi hk
  rw [graph2Rename] at hpairk
  exact BinarySyntaxProof.introduce (BinaryValuesProof.constructor tag)
    ((types.relabel j).relabel k) ((prior.relabel j).relabel k) ((code.relabel j).relabel k)
    ![t.relabel k,q,a] (BinaryValuesProof.fieldsFromPairs tag _ _ _ _ _ _ _ _ _ _ hpk hck hmk hpairk hinner htk)

theorem atMap (tag : Nat) (types prior out code pairs children : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag)) out pairs)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hc : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.typedBinaryCase (BinaryValuesProof.constructor tag) types prior code)) := by
  have hi := MapElimProof.recover (OriginalEnumerationConstructorLayer.tagPayload tag) pairs out code hg hm
  apply MapImageEliminationProof.cases (OriginalEnumerationConstructorLayer.tagPayload tag) pairs code _ hi
  intro beta j Theta payload hj hmem htag
  rw [BinarySyntaxProof.caseRename]
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  exact atPayload tag (types.relabel j) (prior.relabel j) (code.relabel j)
    (pairs.relabel j) (children.relabel j) payload hpj hcj hmem htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryForwardProof
