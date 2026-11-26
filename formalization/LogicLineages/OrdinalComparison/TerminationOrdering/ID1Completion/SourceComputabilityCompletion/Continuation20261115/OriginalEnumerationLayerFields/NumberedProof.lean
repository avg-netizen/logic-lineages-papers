module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedBackwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedProof
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

open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def queries : Fin 2 → Program 7 := ![OriginalEnumerationConstructorLayer.labelRange,OriginalEnumerationConstructorLayer.typeTuples]

theorem rangeAt (xs : Fin 7 → OTerm alpha) (range : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.labelRange range xs))) :
    Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (suc (xs 2)))) := by
  have hs : Nonempty (Derivation body Delta (programGraph (.composition .succ ![.projection 2]) (suc (xs 2)) xs)) := by
    apply compositionValue .succ ![.projection 2] (suc (xs 2)) xs ![xs 2]
    · exact InternalControlGraphSupportProof.successorValue ![xs 2]
    · intro i
      fin_cases i
      exact projectionValue 2 xs
  apply compositionRecover OriginalAscendingRange.range ![(.composition .succ ![.projection 2])] range xs ![suc (xs 2)] hr
  intro i
  fin_cases i
  exact hs

theorem tuplesAt (xs : Fin 7 → OTerm alpha) (tuples : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.typeTuples tuples xs))) :
    Nonempty (Derivation body Delta (graph2 OriginalTypeListsEnumeration.enumeration tuples (xs 3) (xs 0))) :=
  binaryRecover OriginalTypeListsEnumeration.enumeration (.projection 3) (.projection 0)
    tuples (xs 3) (xs 0) xs ht (projectionValue 3 xs) (projectionValue 0 xs)

theorem branchAt (n : Nat) (xs : Fin 7 → OTerm alpha) (out range tuples : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.numbered n) out xs)))
    (hr : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.labelRange range xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.typeTuples tuples xs))) :
    Nonempty (Derivation body Delta (programGraph (OriginalEncodedNumberedEnumerationBranch.branch n) out
      ![range,xs 1,xs 0,xs 5,tuples,xs 5])) := by
  apply compositionRecover (OriginalEncodedNumberedEnumerationBranch.branch n)
    ![OriginalEnumerationConstructorLayer.labelRange,.projection 1,.projection 0,.projection 5,OriginalEnumerationConstructorLayer.typeTuples,.projection 5]
    out xs ![range,xs 1,xs 0,xs 5,tuples,xs 5] hg
  intro i
  fin_cases i
  · exact hr
  · exact projectionValue 1 xs
  · exact projectionValue 0 xs
  · exact projectionValue 5 xs
  · exact ht
  · exact projectionValue 5 xs

theorem forward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.numbered n) out xs)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.numberedCase n (xs 2) (xs 1) (xs 0) (xs 3) (xs 5) code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs _
  intro beta j ys Theta hj hq
  rw [NumberedSyntaxProof.caseRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hhj
  exact NumberedForwardProof.atBranch n ((xs 2).relabel j) ((xs 1).relabel j) ((xs 0).relabel j) ((xs 3).relabel j)
    ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 0) (ys 1)
    (rangeAt _ _ (hq 0)) (tuplesAt _ _ (hq 1)) (branchAt n _ _ _ _ hgj (hq 0) (hq 1)) hhj

theorem backward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.numbered n) out xs)))
    (hh : Nonempty (Derivation body Delta (Targets.numberedCase n (xs 2) (xs 1) (xs 0) (xs 3) (xs 5) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hhj := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
  rw [NumberedSyntaxProof.caseRename] at hhj
  exact NumberedBackwardProof.atBranch n ((xs 2).relabel j) ((xs 1).relabel j) ((xs 0).relabel j) ((xs 3).relabel j)
    ((xs 5).relabel j) (out.relabel j) (code.relabel j) (ys 0) (ys 1)
    (rangeAt _ _ (hq 0)) (tuplesAt _ _ (hq 1)) (branchAt n _ _ _ _ hgj (hq 0) (hq 1)) hhj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedProof
