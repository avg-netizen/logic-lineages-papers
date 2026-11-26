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
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryBackwardProof
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

theorem atPair (n : Nat) (heads prior out code converted pairs payload encoded raw base : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4)) out pairs)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload raw base)))
    (hf : Nonempty (Derivation body Delta (OrdinarySyntaxProof.fields n heads prior code encoded raw base))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have hraw := MapIntroProof.introduce (OriginalEncodedHeadConversion.convert n)
    heads z converted raw z encoded hc (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf)))
  have hpair := OriginalNumberedEnumerationBranch.CrossIntroProof.introduce converted prior pairs payload raw base hp
    (andIntro hraw (andRight (andLeft hf))) hq
  have ht := TagProof.recover 4 TagProof.binaryPayload ![raw,base] code payload (TagProof.binaryAt raw base payload hq) (andRight hf)
  exact MapIntroProof.introduce (OriginalEnumerationConstructorLayer.tagPayload 4) pairs z out code z payload hg hpair ht

theorem atFields (n : Nat) (heads prior out code converted pairs encoded raw base : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4)) out pairs)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hf : Nonempty (Derivation body Delta (OrdinarySyntaxProof.fields n heads prior code encoded raw base))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply programCases InternalPairing.pairing (Fin.cons raw (Fin.cons base Fin.elim0)) _
  intro beta j Theta payload hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [OrdinarySyntaxProof.fieldsRename] at hfj
  exact atPair n (heads.relabel j) (prior.relabel j) (out.relabel j) (code.relabel j)
    (converted.relabel j) (pairs.relabel j) payload (encoded.relabel j) (raw.relabel j) (base.relabel j) hgj hcj hpj hq hfj

theorem atMap (n : Nat) (heads prior out code converted pairs : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4)) out pairs)))
    (hc : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted heads)))
    (hp : Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted prior)))
    (hw : Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OrdinarySyntaxProof.cases n heads prior code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph1Rename] at hcj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hpj
  exact atFields n (heads.relabel j) (prior.relabel j) (out.relabel j) (code.relabel j)
    (converted.relabel j) (pairs.relabel j) (ys 0) (ys 1) (ys 2) hgj hcj hpj hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryBackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryBackwardProof
