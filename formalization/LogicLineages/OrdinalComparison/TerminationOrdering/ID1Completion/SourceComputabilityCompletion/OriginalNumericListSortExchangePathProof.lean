module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathProof
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
open OriginalNumericListSortExchangePathDefinitions OriginalNumericListSortExchangePathSyntaxProof OriginalNumericListSortExchangePathBindingProof OriginalNumericListSortExchangePathCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atNonzero (raw source target left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw source target left right)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,SourceComputabilityFormulaSupportProof.numeral,conjunctionRename,graph1Rename,graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
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
 simp only [conjunctionRename,graph1Rename,graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact atCons ((raw.relabel rho).relabel eta)
   ((source.relabel rho).relabel eta) ((target.relabel rho).relabel eta) ((left.relabel rho).relabel eta) ((right.relabel rho).relabel eta) (head.relabel eta) tail hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let source : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let target : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let left : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let right : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let H := fields r source target left right
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (equal left right)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r source target left right ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r source target left right (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem acceptedPathAt (source target certificate left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields certificate source target left right))) :
 Nonempty (Derivation body Delta (equal left right)) :=
 atRawApply certificate source target left right (allRaw certificate) hf

theorem acceptedPathPreservesSort : OriginalNumericListSortExchangePathTargets.AcceptedPathPreservesSort := by
 intro body alpha source target certificate left right
 obtain ⟨h⟩ := acceptedPathAt source target certificate left right
   (show Nonempty (Derivation body [fields certificate source target left right]
     (fields certificate source target left right)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathProof
