module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionProof
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
open OriginalNumericListSort
open OriginalNumericListSortAbsorptionDefinitions OriginalNumericListSortAbsorptionSyntaxProof OriginalNumericListSortAbsorptionBindingProof OriginalNumericListSortAbsorptionCoreProof OriginalNumericListSortAbsorptionQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consCore (raw head tail x inserted sorted left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply formulaCases (ltF head x) _
 · exact afterAt0 raw head tail x inserted sorted left right
     (withHyp hi _) (withHyp hc _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact beforeCore raw head tail x inserted sorted left right
     (withHyp hc _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem atZero (raw x inserted sorted left right : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hx := headTransport insert inserted raw z ![x] he (andLeft hf)
 have hs := headTransport sort sorted raw z Fin.elim0 he (andLeft (andRight hf))
 exact zeroCore x inserted sorted left right (andIntro hx (andIntro hs (andRight (andRight hf))))

theorem atNonzero (raw x inserted sorted left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
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
 simp only [fields,conjunctionRename,graph1Rename,graph2Rename] at hf'
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
 simp only [conjunctionRename,graph1Rename,graph2Rename] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact consCore ((raw.relabel rho).relabel eta) (head.relabel eta) tail
   ((x.relabel rho).relabel eta) ((inserted.relabel rho).relabel eta)
   ((sorted.relabel rho).relabel eta) ((left.relabel rho).relabel eta) ((right.relabel rho).relabel eta) hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let x : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let inserted : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let sorted : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
 let H := fields r x inserted sorted left right
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (equal left right)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r x inserted sorted left right ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r x inserted sorted left right (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem absorption : OriginalNumericListSortStabilityTargets.Absorption := by
 intro body alpha raw x inserted sorted left right
 have h := atRawApply raw x inserted sorted left right (allRaw raw)
   (show Nonempty (Derivation body [fields raw x inserted sorted left right]
      (fields raw x inserted sorted left right)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨h⟩ := h
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionProof
