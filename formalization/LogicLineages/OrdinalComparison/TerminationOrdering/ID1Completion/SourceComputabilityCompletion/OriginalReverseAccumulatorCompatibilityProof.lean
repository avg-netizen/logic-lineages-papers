module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityProof
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
open OriginalReverseAccumulatorCompatibilityDefinitions OriginalReverseAccumulatorCompatibilitySyntaxProof OriginalReverseAccumulatorCompatibilityBindingProof OriginalReverseAccumulatorCompatibilityCoreProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)

theorem atRawFrom (raw : OTerm alpha) (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let acc1 : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let acc2 : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let suffix : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
 let H := fields r acc1 acc2 suffix left right
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append right left suffix)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r acc1 acc2 suffix left right ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r acc1 acc2 suffix left right (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualCompatibility : OriginalReverseAccumulatorCompatibilityTargets.ActualCompatibility := by
 intro body alpha Delta raw acc1 acc2 suffix left right ha hl hr
 exact atRawApply raw acc1 acc2 suffix left right (allRaw raw) (andIntro ha (andIntro hl hr))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityProof
