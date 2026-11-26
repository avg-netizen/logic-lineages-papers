module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalOriginalPairingOrderArithmeticProof (withHyp formulaCases)
open ListSumInductionDefinitions ListSumInductionSyntaxProof ListSumInductionBindingProof ListSumCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
@[simp] theorem fieldsRename {beta : Type} (raw total : OTerm alpha) (j : alpha → beta) :
 (fields raw total).relabel j = fields (raw.relabel j) (total.relabel j) := by
 simp only [fields,graph1Rename]
@[simp] theorem resultRename {beta : Type} (raw total : OTerm alpha) (j : alpha → beta) :
 (result raw total).relabel j = result (raw.relabel j) (total.relabel j) := by
 simp only [result,InternalPairingSumBounds.weakBound,InternalLessThan.strictLess,orderRename,sucRelabel]

theorem consQuery (raw head tail total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw total))) :
 Nonempty (Derivation body Delta (result raw total)) := by
 apply programCases ListSumBoundDefinitions.sum (Fin.cons tail Fin.elim0) _
 intro beta j Theta tailSum hj ht
 rw [resultRename]
 simp only [consTermRename,emptyRename] at ht
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 exact consCore (raw.relabel j) (head.relabel j) (tail.relabel j) (total.relabel j) tailSum hi' hc' hf' ht

theorem fromFields (raw total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw total))) :
 Nonempty (Derivation body Delta (result raw total)) := by
 apply formulaCases (eqn raw z) _
 · exact zeroCore raw total ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hf _)
 · apply OriginalContextInsertionLengthProof.nonzeroCases raw _
     (show Nonempty (Derivation body ((eqn raw z).not :: Delta) (eqn raw z).not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   intro beta j Theta head tail hj hc
   rw [resultRename]
   have hi' := renameInto (withHyp hi (eqn raw z).not) j Theta hj
   rw [belowRawRename] at hi'
   have hf' := renameInto (withHyp hf (eqn raw z).not) j Theta hj
   rw [fieldsRename] at hf'
   exact consQuery (raw.relabel j) head tail (total.relabel j) hi' hc hf'

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let total : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
 let H := fields r total
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 obtain ⟨h⟩ := fromFields r total hi'
   (show Nonempty (Derivation body Theta H) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualSumBound : ListSumBoundTargets.ActualSumBound := by
 intro body alpha Delta raw total ht
 exact atRawApply raw total (allRaw raw) ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundProof
