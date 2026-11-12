module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalNumericListSort OriginalNumericListSortAdjacentSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionClosureLogicProof (closedApply)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] sort OriginalNumericListSort.insert

theorem adjacentAt (tail x y tailY tailX xy yx left right : OTerm alpha)
 (hy : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailY y tail)))
 (hxy : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode xy x tailY)))
 (hx : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailX x tail)))
 (hyx : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode yx y tailX)))
 (hl : Nonempty (Derivation body Delta (graph1 sort left xy)))
 (hr : Nonempty (Derivation body Delta (graph1 sort right yx)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 apply unaryCases sort tail _
 intro beta1 j1 Theta1 sorted hj1 hsorted
 rw [equalRename]
 have hy_1 := renameInto hy j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hy_1
 have hxy_1 := renameInto hxy j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hxy_1
 have hx_1 := renameInto hx j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hx_1
 have hyx_1 := renameInto hyx j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hyx_1
 have hl_1 := renameInto hl j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hl_1
 have hr_1 := renameInto hr j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at hr_1
 apply unaryCases sort (tailY.relabel j1) _
 intro beta2 j2 Theta2 sortedY hj2 hsortedY
 rw [equalRename]
 have hy_2 := renameInto hy_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hy_2
 have hxy_2 := renameInto hxy_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hxy_2
 have hx_2 := renameInto hx_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hx_2
 have hyx_2 := renameInto hyx_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hyx_2
 have hl_2 := renameInto hl_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hl_2
 have hr_2 := renameInto hr_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hr_2
 have hsorted_2 := renameInto hsorted j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at hsorted_2
 apply unaryCases sort ((tailX.relabel j1).relabel j2) _
 intro beta3 j3 Theta3 sortedX hj3 hsortedX
 rw [equalRename]
 have hy_3 := renameInto hy_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hy_3
 have hxy_3 := renameInto hxy_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hxy_3
 have hx_3 := renameInto hx_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hx_3
 have hyx_3 := renameInto hyx_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hyx_3
 have hl_3 := renameInto hl_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hl_3
 have hr_3 := renameInto hr_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hr_3
 have hsorted_3 := renameInto hsorted_2 j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hsorted_3
 have hsortedY_3 := renameInto hsortedY j3 Theta3 hj3
 simp only [graph1Rename,graph2Rename] at hsortedY_3
 have iy := sortConsRecover (((tailY.relabel j1).relabel j2).relabel j3) (((y.relabel j1).relabel j2).relabel j3) (((tail.relabel j1).relabel j2).relabel j3) ((sorted.relabel j2).relabel j3) (sortedY.relabel j3) hy_3 hsorted_3 hsortedY_3
 have ix := sortConsRecover (((tailX.relabel j1).relabel j2).relabel j3) (((x.relabel j1).relabel j2).relabel j3) (((tail.relabel j1).relabel j2).relabel j3) ((sorted.relabel j2).relabel j3) sortedX hx_3 hsorted_3 hsortedX
 have iyx := sortConsRecover (((xy.relabel j1).relabel j2).relabel j3) (((x.relabel j1).relabel j2).relabel j3) (((tailY.relabel j1).relabel j2).relabel j3) (sortedY.relabel j3) (((left.relabel j1).relabel j2).relabel j3) hxy_3 hsortedY_3 hl_3
 have ixy := sortConsRecover (((yx.relabel j1).relabel j2).relabel j3) (((y.relabel j1).relabel j2).relabel j3) (((tailX.relabel j1).relabel j2).relabel j3) sortedX (((right.relabel j1).relabel j2).relabel j3) hyx_3 hsortedX hr_3
 exact closedApply (OriginalNumericListSortCommutationProof.insertCommutation body beta3
   ((sorted.relabel j2).relabel j3) (((y.relabel j1).relabel j2).relabel j3) (((x.relabel j1).relabel j2).relabel j3) (sortedY.relabel j3) sortedX (((left.relabel j1).relabel j2).relabel j3) (((right.relabel j1).relabel j2).relabel j3))
   (andIntro iy (andIntro iyx (andIntro ix ixy)))

theorem adjacentSwap : OriginalNumericListSortAlgebraTargets.AdjacentSwap := by
 intro body alpha tail x y tailY tailX xy yx left right
 let H := graph2 InternalListCodec.consCode tailY y tail ⊓
   (graph2 InternalListCodec.consCode xy x tailY ⊓
   (graph2 InternalListCodec.consCode tailX x tail ⊓
   (graph2 InternalListCodec.consCode yx y tailX ⊓
   (graph1 sort left xy ⊓ graph1 sort right yx))))
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hv⟩ := adjacentAt tail x y tailY tailX xy yx left right
   (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
   (andLeft (andRight (andRight (andRight h))))
   (andLeft (andRight (andRight (andRight (andRight h)))))
   (andRight (andRight (andRight (andRight (andRight h)))))
 exact ⟨Derivation.implicationIntroduction hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentProof
