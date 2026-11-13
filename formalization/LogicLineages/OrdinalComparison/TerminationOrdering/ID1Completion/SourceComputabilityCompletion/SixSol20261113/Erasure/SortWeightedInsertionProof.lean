module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionProof
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
open SortWeightedDefinitions SortWeightedInductionDefinitions SortWeightedInductionSyntax SortWeightedInductionBindingProof SortWeightedInsertionCore SortWeightedInsertionQueries
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consCore (raw head tail x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params))) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 apply formulaCases (ltF head x) _
 · exact afterAt0 F raw head tail x inserted weight sum params
     (withHyp hi _) (withHyp hc _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 · exact beforeCore F raw head tail x inserted weight sum params
     (withHyp hc _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem atZero (raw x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params))) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 have hx := headTransport insert inserted raw z ![x] he (andLeft hf)
 have hs := headTransport (weighted F) sum raw z params he (andRight (andRight hf))
 exact zeroCore F x inserted weight sum params (andIntro hx (andIntro (andLeft (andRight hf)) hs))

theorem atNonzero (raw x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hne : Nonempty (Derivation body Delta (eqn raw z).not)) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 apply programCases InternalListCodec.headCode ![raw] _
 intro beta rho Theta head hrho hh
 rw [unaryVectorRename] at hh
 rw [resultRename]
 have hi' := renameInto hi rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hn' := renameInto hne rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [fieldsRename] at hf'
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
 simp only [fieldsRename] at hf''
 simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn''
 rw [programRename,unaryVectorRename] at hh'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero
   ((raw.relabel rho).relabel eta) (head.relabel eta) tail hn'' hh' ht
 exact consCore F ((raw.relabel rho).relabel eta) (head.relabel eta) tail
   ((x.relabel rho).relabel eta) ((inserted.relabel rho).relabel eta)
   ((weight.relabel rho).relabel eta) ((sum.relabel rho).relabel eta)
   (fun i => ((params i).relabel rho).relabel eta) hi'' hc hf''

theorem atRawFrom (raw : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params))) :
 Nonempty (Derivation body Delta (AtRaw F raw params)) := by
 let x : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let inserted : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let weight : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let sum : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let ps := fun i => (params i).relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let H := fields F r x inserted weight sum ps
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw F r ps)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 have hf : Nonempty (Derivation body Theta H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have h : Nonempty (Derivation body Theta (result F inserted weight sum ps)) := by
   apply formulaCases (eqn r z) _
   · exact atZero F r x inserted weight sum ps ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
   · exact atNonzero F r x inserted weight sum ps (withHyp hi' _) (withHyp hf _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := h
 exact atRawIntro F raw params ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) (params : Fin k → OTerm alpha) :
 Nonempty (Derivation body Delta (AtRaw F raw params)) :=
 rawInduction F raw params (fun _ _ r ps hi => atRawFrom F r ps hi)

theorem actualInsertion : SortWeightedTargets.ActualInsertion := by
 intro k F body alpha Delta raw x inserted weight sum params hi hw hs
 exact atRawApply F raw x inserted weight sum params (allRaw F raw params)
   (andIntro hi (andIntro hw hs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionProof
