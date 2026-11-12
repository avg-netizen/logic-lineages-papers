module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleSyntaxProof
open OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalContextInsertionSyntaxProof (insertRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem argumentsErase (H : Program 1) (M W : Program 2)
 (raw gamma c erasedType cutoff deleted erased : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw))) :
 Nonempty (Derivation body Delta (ArgumentsWitness H M W erased deleted c)) := by
 obtain ⟨ha⟩ := ha
 apply Nonempty.intro
 apply Derivation.existentialElimination ha
 change Derivation body (ArgumentsMatrix H M W raw gamma c :: Delta.map weaken)
  ((ArgumentsWitness H M W erased deleted c).relabel Sum.inl)
 rw [argumentsWitnessRename]
 let Theta := ArgumentsMatrix H M W raw gamma c :: Delta.map weaken
 have hi' := renameInto hi Sum.inl Theta
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 have he' := renameInto he Sum.inl Theta
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [insertRename] at hi'
 rw [graph3Rename] at he'
 have ht := OriginalUniverseDecoderTransportInterfaceProof.erasureAt H M W true
  (erasedType.relabel Sum.inl) (cutoff.relabel Sum.inl) (deleted.relabel Sum.inl)
  (gamma.relabel Sum.inl) (.var (.inr 0)) (raw.relabel Sum.inl) (erased.relabel Sum.inl) (c.relabel Sum.inl)
  (OriginalUniverseDecoderTransportInductionProof.allRawTransport H M W true (raw.relabel Sum.inl))
  hi' he' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact Classical.choice (argumentsIntro H M W (erased.relabel Sum.inl) (deleted.relabel Sum.inl)
  (c.relabel Sum.inl) (.var (.inr 0)) ht)
theorem atInsertion (H : Program 1) (M W : Program 2)
 (role typ raw gamma c erasedType cutoff deleted erased : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw))) :
 Nonempty (Derivation body Delta (Admissible H M W role typ erased deleted c)) := by
 let A := equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c)
 have hl : Nonempty (Derivation body (A :: Delta) (Admissible H M W role typ erased deleted c)) := by
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht := OriginalUniverseDecoderTransportInterfaceProof.erasureAt H M W false erasedType cutoff deleted gamma typ raw erased c
   (OriginalUniverseDecoderTransportInductionProof.allRawTransport H M W true raw) (withHyp hi A) (withHyp he A) (andRight h)
  exact ⟨orLeft (Classical.choice (andIntro (andLeft h) ht))⟩
 have hr : Nonempty (Derivation body (B :: Delta) (Admissible H M W role typ erased deleted c)) := by
  have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht := argumentsErase H M W raw gamma c erasedType cutoff deleted erased (andRight (andRight h)) (withHyp hi B) (withHyp he B)
  exact ⟨orRight (Classical.choice (andIntro (andLeft h) (andIntro (andLeft (andRight h)) ht)))⟩
 exact ⟨disjunctionElimination (Classical.choice ha)
  (Derivation.implicationIntroduction (Classical.choice hl)) (Derivation.implicationIntroduction (Classical.choice hr))⟩
theorem actualDeletion : OriginalInternalJobAdmissibleDeletionTargets.ActualDeletion := by
 intro body H M W alpha Delta role typ raw gamma c count cutoff deleted erasedType erased ha hl hb hd hk he
 obtain ⟨law⟩ := OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion body alpha Delta count gamma cutoff deleted erasedType
 have hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)) :=
  ⟨Derivation.implicationElimination law (Classical.choice (andIntro hl (andIntro hb (andIntro hd hk))))⟩
 exact atInsertion H M W role typ raw gamma c erasedType cutoff deleted erased ha hi he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionProof
