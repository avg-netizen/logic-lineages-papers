module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF)
open OriginalTwoDeletionInternalVariableArithmeticProof (compareCases)
open OriginalNumericListSortCommutationDefinitions OriginalNumericListSortCommutationCoreProof OriginalNumericListSortCommutationQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem symmetric (x y : OTerm alpha)
 (h : Nonempty (Derivation body Delta (equal x y))) :
 Nonempty (Derivation body Delta (equal y x)) := by
 have h' : Nonempty (Derivation body Delta (eqn x y)) := by simpa only [equalEqn] using h
 obtain ⟨h'⟩ := h'
 simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn y x)) from ⟨symm h'⟩)

theorem swapped (raw x y firstX firstY left right : OTerm alpha)
 (h : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right))) :
 Nonempty (Derivation body Delta (fields raw y x firstY firstX right left)) :=
 andIntro (andLeft (andRight (andRight h)))
   (andIntro (andRight (andRight (andRight h))) (andIntro (andLeft h) (andLeft (andRight h))))

theorem strictCons (raw head tail x y firstX firstY left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply formulaCases (ltF head x) _
 · exact advanceAt0 raw head tail x y firstX firstY left right
     (withHyp hi _) (withHyp hc _) (withHyp hf _) (withHyp hxy _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · have hi' := withHyp hi (ltF head x).not
   have hc' := withHyp hc (ltF head x).not
   have hf' := withHyp hf (ltF head x).not
   have hxy' := withHyp hxy (ltF head x).not
   have hnx : Nonempty (Derivation body ((ltF head x).not :: Delta) (ltF head x).not) :=
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   apply formulaCases (ltF head y) _
   · exact stopAfter raw head tail x y firstX firstY left right
       (withHyp hc' _) (withHyp hf' _) (withHyp hxy' _) (withHyp hnx _) ⟨Derivation.hypothesis List.mem_cons_self⟩
   · exact strictStopBefore raw head tail x y firstX firstY left right
       (withHyp hc' _) (withHyp hf' _) (withHyp hxy' _) (withHyp hnx _) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem zeroAll (x y firstX firstY left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z x y firstX firstY left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply compareCases x y _
 · exact strictZero x y firstX firstY left right (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact equalInputs z x y firstX firstY left right (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact symmetric right left (strictZero y x firstY firstX right left
     (swapped z x y firstX firstY left right (withHyp hf _)) ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem consAll (raw head tail x y firstX firstY left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply compareCases x y _
 · exact strictCons raw head tail x y firstX firstY left right
     (withHyp hi _) (withHyp hc _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact equalInputs raw x y firstX firstY left right (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact symmetric right left (strictCons raw head tail y x firstY firstX right left
     (withHyp hi _) (withHyp hc _) (swapped raw x y firstX firstY left right (withHyp hf _))
     ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCasesProof
