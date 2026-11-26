module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z eqn zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions OriginalTypedArgumentObservationsReverseInternalAccumulatorSyntaxProof OriginalTypedArgumentObservationsReverseInternalAccumulatorBindingProof
open OriginalTypedArgumentObservationsReverseInternalAccumulatorCoreProof OriginalTypedArgumentObservationsReverseInternalAccumulatorQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atZero (front value singleton combined acc left right : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn front z)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right))) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
 have hj := headTransport InternalApplicationValidityStackAppend.append combined front z ![singleton] he (andLeft (andRight hf))
 have hl := headTransport accumulated left front z ![acc] he (andLeft (andRight (andRight hf)))
 exact zeroCore value singleton combined acc left right
   (andIntro (andLeft hf) (andIntro hj (andIntro hl (andRight (andRight (andRight hf))))))

theorem atNonzero (front value singleton combined acc left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front)))
 (hf : Nonempty (Derivation body Delta (fields front value singleton combined acc left right)))
 (hne : Nonempty (Derivation body Delta (eqn front z).not)) :
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right value left)) := by
 apply programCases InternalListCodec.headCode ![front] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 simp only [graph2Rename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fields,conjunctionRename,graph2Rename,zRelabel] at hf'
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
 apply programCases InternalListCodec.tailCode ![front.relabel rho] _
 intro gamma eta Xi tail heta ht
 rw [unaryVectorRename] at ht
 simp only [graph2Rename]
 have hi'' := renameInto hi' eta Xi heta
 have hf'' := renameInto hf' eta Xi heta
 have hn'' := renameInto hn' eta Xi heta
 have hh' := renameInto hh eta Xi heta
 simp only [belowRawRename] at hi''
 simp only [conjunctionRename,graph2Rename,zRelabel] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((front.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact consAt0 ((front.relabel rho).relabel eta) ((value.relabel rho).relabel eta)
   ((singleton.relabel rho).relabel eta) ((combined.relabel rho).relabel eta)
   ((acc.relabel rho).relabel eta) ((left.relabel rho).relabel eta) ((right.relabel rho).relabel eta)
   (head.relabel eta) tail hi'' hf'' hc

theorem atRawFrom (front : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw front))) :
 Nonempty (Derivation body Delta (AtRaw front)) := by
 let value : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let singleton : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let combined : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let acc : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let left : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let right : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let r := front.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
 let H := fields r value singleton combined acc left right
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode right value left)) := by
   apply formulaCases (eqn r z) _
   · exact atZero r value singleton combined acc left right ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero r value singleton combined acc left right (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro front ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (front : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw front)) :=
 rawInduction front (fun _ _ r hi => atRawFrom r hi)

theorem actualAppendSingleton : OriginalTypedArgumentObservationsReverseInternalAccumulatorTargets.AppendSingleton := by
 intro body alpha front value singleton combined acc left right
 have h := atRawApply front value singleton combined acc left right (allRaw front)
   (show Nonempty (Derivation body [fields front value singleton combined acc left right]
      (fields front value singleton combined acc left right)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨h⟩ := h
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorProof
