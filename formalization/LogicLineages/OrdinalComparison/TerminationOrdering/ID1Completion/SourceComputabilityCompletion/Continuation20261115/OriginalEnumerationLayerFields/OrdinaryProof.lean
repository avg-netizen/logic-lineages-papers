module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryBackwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryProof
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
def queries (n : Nat) : Fin 2 → Program 7 := ![OriginalEnumerationConstructorLayer.convertedHeads n,OriginalEnumerationConstructorLayer.ordinaryPairs n]

theorem convertedAt (n : Nat) (xs : Fin 7 → OTerm alpha) (converted : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.convertedHeads n) converted xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) converted (xs 1))) := by
  have he : (fun _ : Fin 1 => (Program.projection 1 : Program 7)) = ![.projection 1] := by
    funext i
    fin_cases i
    rfl
  apply unaryRecover (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (.projection 1) converted (xs 1) xs
  · rw [he]
    exact hc
  · exact projectionValue 1 xs

theorem pairsAt (n : Nat) (xs : Fin 7 → OTerm alpha) (pairs converted : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.ordinaryPairs n) pairs xs)))
    (hc : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.convertedHeads n) converted xs))) :
    Nonempty (Derivation body Delta (graph2 NumericDependencyCross.cross pairs converted (xs 5))) :=
  binaryRecover NumericDependencyCross.cross (OriginalEnumerationConstructorLayer.convertedHeads n) (.projection 5)
    pairs converted (xs 5) xs hp hc (projectionValue 5 xs)

theorem forward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.ordinary n) out xs)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.ordinaryCase n (xs 1) (xs 5) code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) xs _
  intro beta j ys Theta hj hq
  rw [OrdinarySyntaxProof.caseRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hhj
  have hm := unaryRecover (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4))
    (OriginalEnumerationConstructorLayer.ordinaryPairs n) (out.relabel j) (ys 1) (fun i => (xs i).relabel j) hgj (hq 1)
  exact OrdinaryForwardProof.atMap n ((xs 1).relabel j) ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 0) (ys 1)
    hm (convertedAt n _ _ (hq 0)) (pairsAt n _ _ _ (hq 1) (hq 0)) hhj

theorem backward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.ordinary n) out xs)))
    (hh : Nonempty (Derivation body Delta (Targets.ordinaryCase n (xs 1) (xs 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  rw [OrdinarySyntaxProof.caseRename] at hhj
  have hm := unaryRecover (InternalListMap.map (OriginalEnumerationConstructorLayer.tagPayload 4))
    (OriginalEnumerationConstructorLayer.ordinaryPairs n) (out.relabel j) (ys 1) (fun i => (xs i).relabel j) hgj (hq 1)
  exact OrdinaryBackwardProof.atMap n ((xs 1).relabel j) ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 0) (ys 1)
    hm (convertedAt n _ _ (hq 0)) (pairsAt n _ _ _ (hq 1) (hq 0)) hhj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryProof
