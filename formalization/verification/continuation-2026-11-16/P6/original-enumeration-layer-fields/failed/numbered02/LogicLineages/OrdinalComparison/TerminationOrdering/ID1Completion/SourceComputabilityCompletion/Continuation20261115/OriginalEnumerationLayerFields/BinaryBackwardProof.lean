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
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryBackwardProof
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

theorem atFields (tag : Nat) (types prior out code pairs children t q a : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag)) out pairs)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hc : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hf : Nonempty (Derivation body Delta (BinarySyntaxProof.fields (BinaryValuesProof.constructor tag) types prior code t q a))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply programCases InternalPairing.pairing (Fin.cons q (Fin.cons a Fin.elim0)) _
  intro beta j Theta inner hj hi
  simp only [consTermRename,emptyRename] at hi
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [BinarySyntaxProof.fieldsRename] at hfj
  apply programCases InternalPairing.pairing (Fin.cons (t.relabel j) (Fin.cons inner Fin.elim0)) _
  intro gamma k Xi payload hk hpair
  simp only [consTermRename,emptyRename] at hpair
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgk := InternalGraphCompositionFunctionalityProof.renameInto hgj k Xi hk
  rw [graph1Rename] at hgk
  have hpk := InternalGraphCompositionFunctionalityProof.renameInto hpj k Xi hk
  rw [graph2Rename] at hpk
  have hck := InternalGraphCompositionFunctionalityProof.renameInto hcj k Xi hk
  rw [graph2Rename] at hck
  have hfk := InternalGraphCompositionFunctionalityProof.renameInto hfj k Xi hk
  rw [BinarySyntaxProof.fieldsRename] at hfk
  have hik := InternalGraphCompositionFunctionalityProof.renameInto hi k Xi hk
  rw [graph2Rename] at hik
  exact BinaryValuesProof.memberFromFields tag
    ((types.relabel j).relabel k) ((prior.relabel j).relabel k)
    ((out.relabel j).relabel k) ((code.relabel j).relabel k)
    ((pairs.relabel j).relabel k) ((children.relabel j).relabel k)
    payload (inner.relabel k) ((t.relabel j).relabel k) ((q.relabel j).relabel k) ((a.relabel j).relabel k)
    hgk hpk hck hpair hik hfk

theorem atMap (tag : Nat) (types prior out code pairs children : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag)) out pairs)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs types children)))
    (hc : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross children prior prior)))
    (hw : Nonempty (Derivation body Delta (Targets.typedBinaryCase (BinaryValuesProof.constructor tag) types prior code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply BinarySyntaxProof.cases (BinaryValuesProof.constructor tag) types prior code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  exact atFields tag (types.relabel j) (prior.relabel j) (out.relabel j) (code.relabel j)
    (pairs.relabel j) (children.relabel j) (ys 0) (ys 1) (ys 2) hgj hpj hcj hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryBackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryBackwardProof
