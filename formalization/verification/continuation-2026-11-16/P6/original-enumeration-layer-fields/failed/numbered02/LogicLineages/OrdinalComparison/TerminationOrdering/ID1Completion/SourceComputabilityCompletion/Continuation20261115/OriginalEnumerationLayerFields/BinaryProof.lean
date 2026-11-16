module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryBackwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryProof
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

def branch (tag : Nat) : Program 7 := .composition
  (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag))
  (fun _ : Fin 1 => OriginalEnumerationConstructorLayer.typedChildPairs)
def queries : Fin 2 → Program 7 := ![OriginalEnumerationConstructorLayer.childPairs,OriginalEnumerationConstructorLayer.typedChildPairs]

theorem forward (tag : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (branch tag) out xs)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.typedBinaryCase (BinaryValuesProof.constructor tag) (xs 0) (xs 5) code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs _
  intro beta j ys Theta hj hq
  rw [BinarySyntaxProof.caseRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hhj
  have hm := unaryRecover (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag))
    OriginalEnumerationConstructorLayer.typedChildPairs (out.relabel j) (ys 1) (fun i => (xs i).relabel j) hgj (hq 1)
  exact BinaryForwardProof.atMap tag ((xs 0).relabel j) ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 1) (ys 0)
    hm (BinaryValuesProof.pairsAt _ _ _ (hq 1) (hq 0)) (BinaryValuesProof.childrenAt _ _ (hq 0)) hhj

theorem backward (tag : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (branch tag) out xs)))
    (hh : Nonempty (Derivation body Delta (Targets.typedBinaryCase (BinaryValuesProof.constructor tag) (xs 0) (xs 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  rw [BinarySyntaxProof.caseRename] at hhj
  have hm := unaryRecover (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload tag))
    OriginalEnumerationConstructorLayer.typedChildPairs (out.relabel j) (ys 1) (fun i => (xs i).relabel j) hgj (hq 1)
  exact BinaryBackwardProof.atMap tag ((xs 0).relabel j) ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 1) (ys 0)
    hm (BinaryValuesProof.pairsAt _ _ _ (hq 1) (hq 0)) (BinaryValuesProof.childrenAt _ _ (hq 0)) hhj

theorem applicationsForward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.applications out xs)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.typedBinaryCase OriginalRawSyntaxTransport.applicationConstructor (xs 0) (xs 5) code)) := forward 2 xs out code hg hh

theorem applicationsBackward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.applications out xs)))
    (hh : Nonempty (Derivation body Delta (Targets.typedBinaryCase OriginalRawSyntaxTransport.applicationConstructor (xs 0) (xs 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := backward 2 xs out code hg hh

theorem argumentConsForward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.argumentCons out xs)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.typedBinaryCase OriginalRawSyntaxTransport.consConstructor (xs 0) (xs 5) code)) := forward 7 xs out code hg hh

theorem argumentConsBackward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.argumentCons out xs)))
    (hh : Nonempty (Derivation body Delta (Targets.typedBinaryCase OriginalRawSyntaxTransport.consConstructor (xs 0) (xs 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := backward 7 xs out code hg hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryProof
