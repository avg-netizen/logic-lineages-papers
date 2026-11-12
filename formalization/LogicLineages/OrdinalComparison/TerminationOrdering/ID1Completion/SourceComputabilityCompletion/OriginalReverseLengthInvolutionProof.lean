module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservations (reverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalReverseLengthInvolutionDefinitions OriginalReverseLengthInvolutionSyntaxProof OriginalReverseLengthInvolutionBindingProof OriginalReverseLengthInvolutionCoreProof OriginalReverseLengthInvolutionQueryProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)

theorem atRawFrom (raw : OTerm alpha) (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let count : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let mapped : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
 let H := fields r count mapped
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (outputs r count mapped)) := by
   apply formulaCases (eqn r z) _
   · exact zeroCore r count mapped ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r count mapped (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualLaws : OriginalReverseLengthInvolutionTargets.ActualLaws := by
 intro body alpha Delta raw count mapped hl hr
 exact atRawApply raw count mapped (allRaw raw) (andIntro hl hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
