module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename)
open OriginalNumericListSort
open OriginalNumericListSortIdempotenceDefinitions OriginalNumericListSortIdempotenceSyntaxProof OriginalNumericListSortIdempotenceBindingProof OriginalNumericListSortIdempotenceCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atZero (raw sorted again : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw sorted again))) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 have hs := headTransport sort sorted raw z Fin.elim0 he (andLeft hf)
 exact zeroCore sorted again (andIntro hs (andRight hf))

theorem atNonzero (raw sorted again : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw sorted again)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
 apply programCases InternalListCodec.tailCode ![raw.relabel rho] _
 intro gamma eta Xi tail heta ht
 rw [unaryVectorRename] at ht
 rw [equalRename]
 have hi'' := renameInto hi' eta Xi heta
 have hf'' := renameInto hf' eta Xi heta
 have hn'' := renameInto hn' eta Xi heta
 have hh' := renameInto hh eta Xi heta
 simp only [belowRawRename] at hi''
 simp only [conjunctionRename,graph1Rename] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact consCore ((raw.relabel rho).relabel eta) (head.relabel eta) tail
   ((sorted.relabel rho).relabel eta) ((again.relabel rho).relabel eta) hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let sorted : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let again : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
 let H := fields r sorted again
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (equal again sorted)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r sorted again ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r sorted again (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem idempotence : OriginalNumericListSortStabilityTargets.Idempotence := by
 intro body alpha raw sorted again
 have h := atRawApply raw sorted again (allRaw raw)
   (show Nonempty (Derivation body [fields raw sorted again] (fields raw sorted again)) from
     ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨h⟩ := h
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceProof
