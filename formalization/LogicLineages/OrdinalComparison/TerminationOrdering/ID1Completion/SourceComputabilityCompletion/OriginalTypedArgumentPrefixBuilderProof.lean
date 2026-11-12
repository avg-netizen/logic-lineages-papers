module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename)
open OriginalTypedArgumentPrefixBuilder OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentPrefixBuilderRowDefinitions OriginalTypedArgumentPrefixBuilderSyntaxProof OriginalTypedArgumentPrefixBuilderBindingProof OriginalTypedArgumentPrefixBuilderCoreProof OriginalTypedArgumentPrefixBuilderQueryProof
variable (R : Program 2)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atNonzero (raw suffix built parameter mappedValue suffixValue total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw R raw)))
 (hf : Nonempty (Derivation body Delta (fields R raw suffix built parameter mappedValue suffixValue total)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) total built parameter)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [graph2Rename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
 apply programCases InternalListCodec.tailCode ![raw.relabel rho] _
 intro gamma eta Xi tail heta ht
 rw [unaryVectorRename] at ht
 rw [graph2Rename]
 have hi'' := renameInto hi' eta Xi heta
 have hf'' := renameInto hf' eta Xi heta
 have hn'' := renameInto hn' eta Xi heta
 have hh' := renameInto hh eta Xi heta
 simp only [belowRawRename] at hi''
 simp only [conjunctionRename,graph1Rename,graph2Rename] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact consCore R ((raw.relabel rho).relabel eta) (head.relabel eta) tail
   ((suffix.relabel rho).relabel eta) ((built.relabel rho).relabel eta)
   ((parameter.relabel rho).relabel eta) ((mappedValue.relabel rho).relabel eta) ((suffixValue.relabel rho).relabel eta) ((total.relabel rho).relabel eta) hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw R raw))) :
 Nonempty (Derivation body Delta (AtRaw R raw)) := by
 let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let built : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let parameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let mappedValue : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let suffixValue : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let total : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
 let H := fields R r suffix built parameter mappedValue suffixValue total
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw R r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (graph2 (argumentObservations R) total built parameter)) := by
   apply formulaCases (eqn r z) _
   · exact atZero R r suffix built parameter mappedValue suffixValue total ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero R r suffix built parameter mappedValue suffixValue total (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro R raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw R raw)) :=
 rawInduction R raw (fun _ _ r hi => atRawFrom R r hi)

theorem actualAppend : OriginalTypedArgumentPrefixBuilderTargets.ActualAppend := by
 intro R body alpha Delta front suffix built parameter mappedValue suffixValue total hb hm hs ha
 exact atRawApply R front suffix built parameter mappedValue suffixValue total (allRaw R front)
   (andIntro hb (andIntro hm (andIntro hs ha)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderProof
