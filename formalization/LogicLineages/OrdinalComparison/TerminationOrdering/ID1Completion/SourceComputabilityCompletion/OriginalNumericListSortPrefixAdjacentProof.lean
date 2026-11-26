module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixAdjacentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalNumericListSort OriginalNumericListSortAdjacentSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] sort

theorem prefixAdjacentAt (front tail x y tailY tailX xy yx left right outA outB : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailY y tail)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode xy x tailY)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailX x tail)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode yx y tailX)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append left front xy)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append right front yx)))
 (h6 : Nonempty (Derivation body Delta (graph1 sort outA left)))
 (h7 : Nonempty (Derivation body Delta (graph1 sort outB right)))
 : Nonempty (Derivation body Delta (equal outA outB)) := by
 apply unaryCases sort xy _
 intro beta1 j1 Theta1 a hj1 ha
 rw [equalRename]
 have h0_1 := renameInto h0 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h0_1
 have h1_1 := renameInto h1 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h1_1
 have h2_1 := renameInto h2 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h2_1
 have h3_1 := renameInto h3 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h3_1
 have h4_1 := renameInto h4 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h4_1
 have h5_1 := renameInto h5 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h5_1
 have h6_1 := renameInto h6 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h6_1
 have h7_1 := renameInto h7 j1 Theta1 hj1
 simp only [graph1Rename,graph2Rename] at h7_1
 apply unaryCases sort (yx.relabel j1) _
 intro beta2 j2 Theta2 b hj2 hb
 rw [equalRename]
 have h0_2 := renameInto h0_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h0_2
 have h1_2 := renameInto h1_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h1_2
 have h2_2 := renameInto h2_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h2_2
 have h3_2 := renameInto h3_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h3_2
 have h4_2 := renameInto h4_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h4_2
 have h5_2 := renameInto h5_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h5_2
 have h6_2 := renameInto h6_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h6_2
 have h7_2 := renameInto h7_1 j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at h7_2
 have ha_2 := renameInto ha j2 Theta2 hj2
 simp only [graph1Rename,graph2Rename] at ha_2
 have he := OriginalNumericListSortAdjacentProof.adjacentAt ((tail.relabel j1).relabel j2) ((x.relabel j1).relabel j2) ((y.relabel j1).relabel j2) ((tailY.relabel j1).relabel j2) ((tailX.relabel j1).relabel j2) ((xy.relabel j1).relabel j2) ((yx.relabel j1).relabel j2) (a.relabel j2) b
   h0_2 h1_2 h2_2 h3_2 ha_2 hb
 exact OriginalNumericListSortPrefixProof.prefixAt ((front.relabel j1).relabel j2) ((xy.relabel j1).relabel j2) ((yx.relabel j1).relabel j2) ((left.relabel j1).relabel j2) ((right.relabel j1).relabel j2) (a.relabel j2) b ((outA.relabel j1).relabel j2) ((outB.relabel j1).relabel j2)
   (andIntro h4_2 (andIntro h5_2 (andIntro ha_2 (andIntro hb (andIntro he (andIntro h6_2 h7_2))))))

theorem prefixAdjacentSwap : OriginalNumericListSortPrefixTargets.PrefixAdjacentSwap := by
 intro body alpha front tail x y tailY tailX xy yx left right outA outB
 let H := graph2 InternalListCodec.consCode tailY y tail ⊓ (graph2 InternalListCodec.consCode xy x tailY ⊓ (graph2 InternalListCodec.consCode tailX x tail ⊓ (graph2 InternalListCodec.consCode yx y tailX ⊓ (graph2 InternalApplicationValidityStackAppend.append left front xy ⊓ (graph2 InternalApplicationValidityStackAppend.append right front yx ⊓ (graph1 sort outA left ⊓ (graph1 sort outB right)))))))
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hv⟩ := prefixAdjacentAt front tail x y tailY tailX xy yx left right outA outB
   (andLeft h)
   (andLeft (andRight h))
   (andLeft (andRight (andRight h)))
   (andLeft (andRight (andRight (andRight h))))
   (andLeft (andRight (andRight (andRight (andRight h)))))
   (andLeft (andRight (andRight (andRight (andRight (andRight h))))))
   (andLeft (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
   (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
 exact ⟨Derivation.implicationIntroduction hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixAdjacentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixAdjacentProof
