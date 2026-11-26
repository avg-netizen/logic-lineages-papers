module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions (accumulated)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalReverseAccumulatorCompatibilityDefinitions OriginalReverseAccumulatorCompatibilitySyntaxProof OriginalReverseAccumulatorCompatibilityBindingProof OriginalReverseAccumulatorCompatibilityQueryProof

theorem atZero (raw acc1 acc2 suffix left right : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw acc1 acc2 suffix left right))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append right left suffix)) := by
 have hl := headTransport accumulated left raw z ![acc1] he (andLeft (andRight hf))
 have hr := headTransport accumulated right raw z ![acc2] he (andRight (andRight hf))
 have el := valueUnique accumulated left acc1 ![z,acc1] hl (OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof.zero acc1)
 have er := valueUnique accumulated right acc2 ![z,acc2] hr (OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof.zero acc2)
 have hp := headTransport InternalApplicationValidityStackAppend.append acc2 acc1 left ![suffix]
   (by obtain ⟨el⟩ := el; exact ⟨symm el⟩) (andLeft hf)
 exact outputTransport InternalApplicationValidityStackAppend.append acc2 right ![left,suffix]
   (by obtain ⟨er⟩ := er; exact ⟨symm er⟩) hp

theorem atCons (raw head tail acc1 acc2 suffix left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw acc1 acc2 suffix left right)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append right left suffix)) := by
 apply consCases raw head tail acc1 left _ hc (andLeft (andRight hf))
 intro beta rho Theta next1 hrho hn1 hl
 simp only [graph2Rename]
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename] at hf'
 have hc' := renameInto hc rho Theta hrho
 rw [graph2Rename] at hc'
 apply consCases (raw.relabel rho) (head.relabel rho) (tail.relabel rho)
   (acc2.relabel rho) (right.relabel rho) _ hc' (andRight (andRight hf'))
 intro gamma eta Xi next2 heta hn2 hr
 simp only [graph2Rename]
 have hi'' := renameInto hi' eta Xi heta
 rw [belowRawRename] at hi''
 have hf'' := renameInto hf' eta Xi heta
 simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename] at hf''
 have hc'' := renameInto hc' eta Xi heta
 rw [graph2Rename] at hc''
 have hn1' := renameInto hn1 eta Xi heta
 have hl' := renameInto hl eta Xi heta
 rw [graph2Rename] at hn1' hl'
 have happ := InternalApplicationValidityStackAppendListProof.consBackward
   (next1.relabel eta) ((head.relabel rho).relabel eta) ((acc1.relabel rho).relabel eta)
   ((suffix.relabel rho).relabel eta) ((acc2.relabel rho).relabel eta) next2 hn1' (andLeft hf'') hn2
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent
   ((raw.relabel rho).relabel eta) ((head.relabel rho).relabel eta) ((tail.relabel rho).relabel eta) hc''
 exact belowRawApply ((raw.relabel rho).relabel eta) ((tail.relabel rho).relabel eta)
   (next1.relabel eta) next2 ((suffix.relabel rho).relabel eta)
   ((left.relabel rho).relabel eta) ((right.relabel rho).relabel eta) hi'' hb (andIntro happ (andIntro hl' hr))

theorem atNonzero (raw acc1 acc2 suffix left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw acc1 acc2 suffix left right)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append right left suffix)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases raw _ hne
 intro beta rho Theta head tail hrho hc
 simp only [graph2Rename]
 have hi' := renameInto hi rho Theta hrho
 rw [belowRawRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fields,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename] at hf'
 exact atCons (raw.relabel rho) head tail (acc1.relabel rho) (acc2.relabel rho)
   (suffix.relabel rho) (left.relabel rho) (right.relabel rho) hi' hf' hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityCoreProof
