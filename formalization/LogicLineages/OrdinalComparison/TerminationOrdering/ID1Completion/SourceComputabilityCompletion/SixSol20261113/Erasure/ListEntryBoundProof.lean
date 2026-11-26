module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalTagArithmeticSyntaxProof (sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open OriginalContextInsertionSyntaxProof (lengthRename)
open ListEntryInductionDefinitions ListEntryInductionSyntaxProof ListEntryInductionBindingProof
open ListEntryCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem fieldsRename {beta : Type} (raw count index value total : OTerm alpha) (j : alpha → beta) :
 (fields raw count index value total).relabel j =
 fields (raw.relabel j) (count.relabel j) (index.relabel j) (value.relabel j) (total.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,OriginalContextInsertion.Below,orderRename,graph1Rename,graph2Rename]
@[simp] theorem resultRename {beta : Type} (raw count index value total : OTerm alpha) (j : alpha → beta) :
 (result raw count index value total).relabel j =
 result (raw.relabel j) (count.relabel j) (index.relabel j) (value.relabel j) (total.relabel j) := by
 simp only [result,InternalPairingSumBounds.weakBound,InternalLessThan.strictLess,orderRename,sucRelabel]

theorem successorQuery (raw head tail count index value total pred tailSum : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total)))
 (he : Nonempty (Derivation body Delta (eqn index (suc pred))))
 (hts : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
 intro beta j Theta tailCount hj ht
 rw [resultRename]
 simp only [consTermRename,emptyRename] at ht
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 have he' := renameInto he j Theta hj
 simp only [InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel] at he'
 have hts' := renameInto hts j Theta hj
 rw [graph1Rename] at hts'
 exact atSuccessor (raw.relabel j) (head.relabel j) (tail.relabel j) (count.relabel j)
   (index.relabel j) (value.relabel j) (total.relabel j) (pred.relabel j) tailCount (tailSum.relabel j)
   hi' hc' hf' he' ht hts'

theorem consKnown (raw head tail count index value total tailSum : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total)))
 (hts : Nonempty (Derivation body Delta (graph1 ListSumBoundDefinitions.sum tailSum tail))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 apply InternalControlGraphSupportProof.zeroSuccessorCases Delta index _
 · exact atZero raw head tail count index value total tailSum (withHyp hc _) (withHyp hf _)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hts _)
 · intro beta j Theta pred hj he
   rw [resultRename]
   have hi' := renameInto hi j Theta hj
   rw [belowRawRename] at hi'
   have hc' := renameInto hc j Theta hj
   rw [graph2Rename] at hc'
   have hf' := renameInto hf j Theta hj
   rw [fieldsRename] at hf'
   have hts' := renameInto hts j Theta hj
   rw [graph1Rename] at hts'
   exact successorQuery (raw.relabel j) (head.relabel j) (tail.relabel j)
     (count.relabel j) (index.relabel j) (value.relabel j) (total.relabel j) pred (tailSum.relabel j)
     hi' hc' hf' he hts'

theorem consAt (raw head tail count index value total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 apply programCases ListSumBoundDefinitions.sum (Fin.cons tail Fin.elim0) _
 intro beta j Theta tailSum hj hts
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hts
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 exact consKnown (raw.relabel j) (head.relabel j) (tail.relabel j) (count.relabel j)
   (index.relabel j) (value.relabel j) (total.relabel j) tailSum hi' hc' hf' hts
theorem fromFields (raw count index value total : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value total))) :
 Nonempty (Derivation body Delta (result raw count index value total)) := by
 have hn := OriginalAllPositionContextDeleteInductionCoreProof.contextNonzero count raw index
   (andLeft hf) (andLeft (andRight hf))
 apply OriginalContextInsertionLengthProof.nonzeroCases raw _ hn
 intro beta j Theta head tail hj hc
 rw [resultRename]
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 exact consAt (raw.relabel j) head tail (count.relabel j) (index.relabel j) (value.relabel j) (total.relabel j) hi' hc hf'

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let count : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let total : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let H := fields r count index value total
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 obtain ⟨h⟩ := fromFields r count index value total hi'
   (show Nonempty (Derivation body Theta H) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualEntryBound : ListSumBoundTargets.ActualEntryBound := by
 intro body alpha Delta raw count index value total hl hb hv hs
 exact atRawApply raw count index value total (allRaw raw) (andIntro hl (andIntro hb (andIntro hv hs)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListEntryBoundProof
