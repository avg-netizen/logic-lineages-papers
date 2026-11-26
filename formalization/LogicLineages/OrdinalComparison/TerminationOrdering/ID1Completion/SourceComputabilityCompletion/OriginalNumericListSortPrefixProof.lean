module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixProof
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
open OriginalNumericListSortPrefixDefinitions OriginalNumericListSortPrefixSyntaxProof OriginalNumericListSortPrefixBindingProof OriginalNumericListSortPrefixCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atNonzero (raw tailA tailB left right a b outA outB : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw tailA tailB left right a b outA outB)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (equal outA outB)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf'
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
 simp only [conjunctionRename,equalRename,graph1Rename,graph2Rename] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact atCons ((raw.relabel rho).relabel eta)
   ((tailA.relabel rho).relabel eta) ((tailB.relabel rho).relabel eta) ((left.relabel rho).relabel eta) ((right.relabel rho).relabel eta) ((a.relabel rho).relabel eta) ((b.relabel rho).relabel eta) ((outA.relabel rho).relabel eta) ((outB.relabel rho).relabel eta) (head.relabel eta) tail hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let tailA : OTerm (alpha ⊕ Fin 8) := .var (.inr 0)
 let tailB : OTerm (alpha ⊕ Fin 8) := .var (.inr 1)
 let left : OTerm (alpha ⊕ Fin 8) := .var (.inr 2)
 let right : OTerm (alpha ⊕ Fin 8) := .var (.inr 3)
 let a : OTerm (alpha ⊕ Fin 8) := .var (.inr 4)
 let b : OTerm (alpha ⊕ Fin 8) := .var (.inr 5)
 let outA : OTerm (alpha ⊕ Fin 8) := .var (.inr 6)
 let outB : OTerm (alpha ⊕ Fin 8) := .var (.inr 7)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 8)
 let H := fields r tailA tailB left right a b outA outB
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (equal outA outB)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r tailA tailB left right a b outA outB ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r tailA tailB left right a b outA outB (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem prefixAt (front tailA tailB left right a b outA outB : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields front tailA tailB left right a b outA outB))) :
 Nonempty (Derivation body Delta (equal outA outB)) :=
 atRawApply front tailA tailB left right a b outA outB (allRaw front) hf

theorem prefixCongruence : OriginalNumericListSortPrefixTargets.PrefixCongruence := by
 intro body alpha front tailA tailB left right a b outA outB
 obtain ⟨h⟩ := prefixAt front tailA tailB left right a b outA outB
   (show Nonempty (Derivation body [fields front tailA tailB left right a b outA outB]
     (fields front tailA tailB left right a b outA outB)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixProof
