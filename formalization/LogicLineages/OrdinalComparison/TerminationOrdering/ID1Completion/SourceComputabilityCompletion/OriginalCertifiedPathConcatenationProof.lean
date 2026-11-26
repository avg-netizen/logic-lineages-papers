module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationProof
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
open OriginalCertifiedPathConcatenationDefinitions OriginalCertifiedPathConcatenationSyntaxProof OriginalCertifiedPathConcatenationBindingProof OriginalCertifiedPathConcatenationCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {edge : Program 3}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atNonzero (raw source middle target right combined : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw edge raw)))
 (hf : Nonempty (Derivation body Delta (fields edge raw source middle target right combined)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (result edge source target combined)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [resultRename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
 apply programCases InternalListCodec.tailCode ![raw.relabel rho] _
 intro gamma eta Xi tail heta ht
 rw [unaryVectorRename] at ht
 rw [resultRename]
 have hi'' := renameInto hi' eta Xi heta
 have hf'' := renameInto hf' eta Xi heta
 have hn'' := renameInto hn' eta Xi heta
 have hh' := renameInto hh eta Xi heta
 simp only [belowRawRename] at hi''
 simp only [conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact atCons ((raw.relabel rho).relabel eta)
   ((source.relabel rho).relabel eta) ((middle.relabel rho).relabel eta) ((target.relabel rho).relabel eta) ((right.relabel rho).relabel eta) ((combined.relabel rho).relabel eta) (head.relabel eta) tail hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw edge raw))) :
 Nonempty (Derivation body Delta (AtRaw edge raw)) := by
 let source : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let middle : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let target : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let combined : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
 let H := fields edge r source middle target right combined
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw edge r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (result edge source target combined)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r source middle target right combined ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r source middle target right combined (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw edge raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualConcatenation : OriginalCertifiedPathConcatenationTargets.ActualConcatenation := by
 intro edge body alpha Delta raw source middle target right combined hp hq ha
 exact atRawApply raw source middle target right combined (allRaw raw)
   (andIntro hp (andIntro hq ha))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationProof
