module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalOriginalOrderSyntaxProof (ltF orderRename sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRawListRecursionSyntaxProof (consTermRename emptyRename)
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open OriginalContextInsertionSyntaxProof (lengthRename)
open ObservationDescentLookupDefinitions ObservationDescentLookupSyntaxProof ObservationDescentLookupBindingProof
open ObservationDescentLookupCore
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem fieldsRename {beta : Type} (raw count index value : OTerm alpha) (j : alpha → beta) :
 (fields raw count index value).relabel j =
 fields (raw.relabel j) (count.relabel j) (index.relabel j) (value.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,OriginalContextInsertion.Below,orderRename,graph2Rename]

theorem successorQuery (raw head tail count index value pred : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value)))
 (he : Nonempty (Derivation body Delta (eqn index (suc pred)))) :
 Nonempty (Derivation body Delta (ltF value raw)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
 intro beta j Theta tailCount hj ht
 rw [orderRename]
 simp only [consTermRename,emptyRename] at ht
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 have he' := renameInto he j Theta hj
 simp only [InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel] at he'
 exact atSuccessor (raw.relabel j) (head.relabel j) (tail.relabel j) (count.relabel j)
   (index.relabel j) (value.relabel j) (pred.relabel j) tailCount hi' hc' hf' he' ht

theorem consAt (raw head tail count index value : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value))) :
 Nonempty (Derivation body Delta (ltF value raw)) := by
 apply InternalControlGraphSupportProof.zeroSuccessorCases Delta index _
 · exact atZero raw head tail count index value (withHyp hc _) (withHyp hf _)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 · intro beta j Theta pred hj he
   rw [orderRename]
   have hi' := renameInto hi j Theta hj
   rw [belowRawRename] at hi'
   have hc' := renameInto hc j Theta hj
   rw [graph2Rename] at hc'
   have hf' := renameInto hf j Theta hj
   rw [fieldsRename] at hf'
   exact successorQuery (raw.relabel j) (head.relabel j) (tail.relabel j)
     (count.relabel j) (index.relabel j) (value.relabel j) pred hi' hc' hf' he

theorem fromFields (raw count index value : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hf : Nonempty (Derivation body Delta (fields raw count index value))) :
 Nonempty (Derivation body Delta (ltF value raw)) := by
 have hn := OriginalAllPositionContextDeleteInductionCoreProof.contextNonzero count raw index
   (andLeft hf) (andLeft (andRight hf))
 apply OriginalContextInsertionLengthProof.nonzeroCases raw _ hn
 intro beta j Theta head tail hj hc
 rw [orderRename]
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 exact consAt (raw.relabel j) head tail (count.relabel j) (index.relabel j) (value.relabel j) hi' hc hf'

theorem atRawFrom (raw : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw))) :
 Nonempty (Derivation body Delta (AtRaw raw)) := by
 let count : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let value : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let H := fields r count index value
 let Theta := H :: Delta.map (fun q => q.relabel Sum.inl)
 have hi' : Nonempty (Derivation body Theta (BelowRaw r)) := by
   have h := renameInto hi Sum.inl Theta (by
     intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
   simpa only [belowRawRename] using h
 obtain ⟨h⟩ := fromFields r count index value hi'
   (show Nonempty (Derivation body Theta H) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact atRawIntro raw ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw raw)) :=
 rawInduction raw (fun _ _ r hi => atRawFrom r hi)

theorem actualLookupDescent (raw count index value : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count raw)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index raw))) :
 Nonempty (Derivation body Delta (ltF value raw)) :=
 atRawApply raw count index value (allRaw raw) (andIntro hl (andIntro hb hv))

theorem actualTypedLookupDescent : ObservationDescentTargets.ActualTypedLookupDescent := by
 intro body alpha Delta list count index typed typ child hl hb hv hp
 exact InternalOriginalPairingOrderArithmeticProof.weakStrictTrans child typed list
   (ObservationDescentPairProof.pairRightBound typed typ child hp)
   (actualLookupDescent list count index typed hl hb hv)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentLookupProof
