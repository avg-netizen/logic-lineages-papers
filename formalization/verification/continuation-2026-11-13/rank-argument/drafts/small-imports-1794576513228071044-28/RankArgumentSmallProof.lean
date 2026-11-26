module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSmallProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedSubst)
open OriginalContextInsertionSyntaxProof (lengthSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalOrderProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalTagArithmeticSupportProof (trans symm congSuc)
open InternalAdditionLawsProof (leftZero leftSuccessor)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSupportProof
open RankArgumentLocalProof RankArgumentSyntax

theorem zeroBelow (count : OTerm alpha) : Nonempty (Derivation body Delta (ltF z (suc count))) := by
 apply actualOriginalOrderIntroduction body alpha Delta z (suc count) count
 rw [InternalSourceInversionSupportProof.onEquality]
 exact ⟨leftZero (suc count)⟩
theorem successorBelow (index count : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (ltF index count))) :
 Nonempty (Derivation body Delta (ltF (suc index) (suc count))) := by
 apply orderCases Delta index count _ hi
 intro beta j Theta gap hj hg
 simp only [orderRename,sucRelabel]
 obtain ⟨hg⟩ := hg
 apply actualOriginalOrderIntroduction body beta Theta (suc (index.relabel j)) (suc (count.relabel j)) gap
 rw [InternalSourceInversionSupportProof.onEquality]
 exact ⟨trans (leftSuccessor (index.relabel j) (suc gap)) (congSuc hg)⟩

theorem headAtCount (list typed tail typ child bound count : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (AllSmall list bound)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list typed tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count tail))) :
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child bound)) :=
 smallApply list bound (suc count) z typed typ child hs
   (OriginalContextInsertionLengthProof.lengthCons list typed tail count hc hl) (zeroBelow count)
   (OriginalAllPositionContextDeleteBaseProof.lookupZero list typed tail hc) hp

theorem headSmall (list typed tail typ child bound : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (AllSmall list bound)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list typed tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child))) :
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child bound)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons tail Fin.elim0) _
 intro beta j Theta count hj hl
 rw [orderRename]
 simp only [consTermRename,emptyRename] at hl
 have hs' := renameInto hs j Theta hj
 rw [smallRename] at hs'
 have hc' := renameInto hc j Theta hj
 have hp' := renameInto hp j Theta hj
 rw [graph2Rename] at hc' hp'
 exact headAtCount (list.relabel j) (typed.relabel j) (tail.relabel j) (typ.relabel j)
   (child.relabel j) (bound.relabel j) count hs' hc' hp' hl

theorem tailSmall (list head tail bound : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (AllSmall list bound)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail))) :
 Nonempty (Derivation body Delta (AllSmall tail bound)) := by
 unfold AllSmall
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let j : alpha → alpha ⊕ Fin 5 := Sum.inl
 let count : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let typed : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let typ : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let child : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := OriginalContextInsertion.lengthGraph count (tail.relabel j) ⊓
   (OriginalContextInsertion.Below index count ⊓
    (graph2 InternalRawListRecursion.lookup typed index (tail.relabel j) ⊓
     graph2 InternalPairing.pairing typed typ child))
 let Theta := A :: Delta.map (fun f => f.relabel j)
 have inc : ∀ f ∈ Delta, f.relabel j ∈ Theta := fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have hs' := renameInto hs j Theta inc
 rw [smallRename] at hs'
 have hc' := renameInto hc j Theta inc
 rw [graph2Rename] at hc'
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff
   (list.relabel j) (head.relabel j) (tail.relabel j) index typed hc'
 obtain ⟨hv⟩ := andLeft (andRight (andRight h))
 have hv' := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight hiff) hv)
 obtain ⟨out⟩ := smallApply (list.relabel j) (bound.relabel j) (suc count) (suc index) typed typ child hs'
   (OriginalContextInsertionLengthProof.lengthCons _ _ _ count hc' (andLeft h))
   (successorBelow index count (andLeft (andRight h))) hv' (andRight (andRight (andRight h)))
 exact ⟨Derivation.implicationIntroduction out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSmallProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSmallProof
