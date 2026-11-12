module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof
open InternalRecursionClosureLogicProof (closedApply)
open InternalPositiveUnfoldingSupportProof (weakenClosed)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof (strictTrans)
open OriginalContextTwoDeletionCoreProof (secondInput)
open OriginalNumericListSort OriginalNumericListSortInsertionProof
open OriginalNumericListSortCommutationDefinitions OriginalNumericListSortCommutationBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem notReverse (x y : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF x y))) :
 Nonempty (Derivation body Delta (ltF y x).not) := by
 have hl := strictTrans x y x (withHyp h (ltF y x))
   (show Nonempty (Derivation body (ltF y x :: Delta) (ltF y x)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨hn⟩ := InternalOriginalOrderProof.actualOriginalOrderIrreflexivity body alpha x
 obtain ⟨hl⟩ := hl
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
   (weakenClosed hn (ltF y x :: Delta)) hl)⟩

theorem equalInputs (raw x y firstX firstY left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (he : Nonempty (Derivation body Delta (eqn x y))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 obtain ⟨he⟩ := he
 have hfy := secondInput insert firstY raw y x ⟨symm he⟩ (andLeft (andRight (andRight hf)))
 have ef := valueUnique insert firstX firstY ![raw,x] (andLeft hf) hfy
 obtain ⟨ef⟩ := ef
 have hr := headTransport insert right firstY firstX ![x] ⟨symm ef⟩ (andRight (andRight (andRight hf)))
 have hr' := secondInput insert right firstX x y ⟨he⟩ hr
 simpa only [equalEqn] using valueUnique insert left right ![firstX,y] (andLeft (andRight hf)) hr'

theorem strictZero (x y firstX firstY left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hx := nilRecover x firstX (andLeft hf)
 have hy := nilRecover y firstY (andLeft (andRight (andRight hf)))
 have hl := afterRecover firstX x z y firstY left hx (andLeft (andRight (andRight hf))) (andLeft (andRight hf)) hxy
 have hr := beforeRecover firstY y z x right hy (andRight (andRight (andRight hf))) (notReverse x y hxy)
 simpa only [equalEqn] using valueUnique InternalListCodec.consCode left right ![x,firstY] hl hr

theorem strictStopBefore (raw head tail x y firstX firstY left right : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hnx : Nonempty (Derivation body Delta (ltF head x).not))
 (hny : Nonempty (Derivation body Delta (ltF head y).not)) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hx := beforeRecover raw head tail x firstX hc (andLeft hf) hnx
 have hy := beforeRecover raw head tail y firstY hc (andLeft (andRight (andRight hf))) hny
 have hl := afterRecover firstX x raw y firstY left hx (andLeft (andRight (andRight hf))) (andLeft (andRight hf)) hxy
 have hr := beforeRecover firstY y raw x right hy (andRight (andRight (andRight hf))) (notReverse x y hxy)
 simpa only [equalEqn] using valueUnique InternalListCodec.consCode left right ![x,firstY] hl hr

theorem strictStopAfter (raw head tail x y firstX firstY left right insertedY : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hnx : Nonempty (Derivation body Delta (ltF head x).not))
 (hhy : Nonempty (Derivation body Delta (ltF head y)))
 (hy : Nonempty (Derivation body Delta (graph2 insert insertedY tail y))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hx := beforeRecover raw head tail x firstX hc (andLeft hf) hnx
 have hcY := afterRecover raw head tail y insertedY firstY hc hy (andLeft (andRight (andRight hf))) hhy
 have hl := afterRecover firstX x raw y firstY left hx (andLeft (andRight (andRight hf))) (andLeft (andRight hf)) hxy
 have hr := beforeRecover firstY head insertedY x right hcY (andRight (andRight (andRight hf))) hnx
 simpa only [equalEqn] using valueUnique InternalListCodec.consCode left right ![x,firstY] hl hr

theorem strictAdvance (raw head tail x y firstX firstY left right tx ty tl tr : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x y firstX firstY left right)))
 (hxy : Nonempty (Derivation body Delta (ltF x y)))
 (hhx : Nonempty (Derivation body Delta (ltF head x)))
 (htx : Nonempty (Derivation body Delta (graph2 insert tx tail x)))
 (hty : Nonempty (Derivation body Delta (graph2 insert ty tail y)))
 (htl : Nonempty (Derivation body Delta (graph2 insert tl tx y)))
 (htr : Nonempty (Derivation body Delta (graph2 insert tr ty x))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hhy := strictTrans head x y hhx hxy
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have ht := belowRawApply raw tail x y tx ty tl tr hi hb (andIntro htx (andIntro htl (andIntro hty htr)))
 have hx := afterRecover raw head tail x tx firstX hc htx (andLeft hf) hhx
 have hy := afterRecover raw head tail y ty firstY hc hty (andLeft (andRight (andRight hf))) hhy
 have hl := afterRecover firstX head tx y tl left hx htl (andLeft (andRight hf)) hhy
 have hr := afterRecover firstY head ty x tr right hy htr (andRight (andRight (andRight hf))) hhx
 have he : Nonempty (Derivation body Delta (eqn tl tr)) := by simpa only [equalEqn] using ht
 have hl' := secondInput InternalListCodec.consCode left head tl tr he hl
 simpa only [equalEqn] using valueUnique InternalListCodec.consCode left right ![head,tr] hl' hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationCoreProof
