module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem acceptedTags (H : Program 1) (M W : Program 2)
 (types raw gamma c tag payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))) :
 Nonempty (Derivation body Delta (equal tag (numeral 6) ⊔ equal tag (numeral 7))) := by
 apply formulaCases (equal tag (numeral 6)) _
 · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
 · have h6 : Nonempty (Derivation body ((equal tag (numeral 6)).not :: Delta) ((equal tag (numeral 6)).not)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   apply formulaCases (equal tag (numeral 7)) _
   · exact ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩
   · have h7 : Nonempty (Derivation body ((equal tag (numeral 7)).not :: (equal tag (numeral 6)).not :: Delta)
        ((equal tag (numeral 7)).not)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
     obtain ⟨hf⟩ := OriginalUniverseDecoderInternalAcceptanceRejectedProof.argumentsRejected H M W raw tag payload types gamma c
      (withHyp (withHyp hp _) _) (andIntro (withHyp h6 _) h7) (withHyp (withHyp ha _) _)
     exact ⟨Derivation.explosion hf⟩

theorem witnessTags (H : Program 1) (M W : Program 2)
 (raw gamma c tag payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))) :
 Nonempty (Derivation body Delta (equal tag (numeral 6) ⊔ equal tag (numeral 7))) := by
 obtain ⟨ha⟩ := ha
 apply Nonempty.intro
 apply Derivation.existentialElimination ha
 change Derivation body (ArgumentsMatrix H M W raw gamma c :: Delta.map weaken)
  ((equal tag (numeral 6) ⊔ equal tag (numeral 7)).relabel Sum.inl)
 have hp' := renameInto hp Sum.inl (ArgumentsMatrix H M W raw gamma c :: Delta.map weaken)
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph2Rename] at hp'
 let Theta : List (Formula (alpha ⊕ Fin 1)) := ArgumentsMatrix H M W raw gamma c :: Delta.map weaken
 have hm : Nonempty (Derivation body Theta (ArgumentsMatrix H M W raw gamma c)) :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 dsimp only [ArgumentsMatrix] at hm
 have ht := acceptedTags (body:=body) (Delta:=Theta) H M W (.var (.inr 0))
  (raw.relabel Sum.inl) (gamma.relabel Sum.inl) (c.relabel Sum.inl)
  (tag.relabel Sum.inl) (payload.relabel Sum.inl) hm hp'
 simpa only [OriginalUniverseDecoderInternalBooleanProof.orRename,equalRename,GuardedSourceSyntaxProof.numeralRename] using Classical.choice ht


theorem supportedReturn : OriginalInternalJobAdmissibleTargets.SupportedReturn := by
 intro body H M W alpha Delta role typ raw gamma c tag payload ha hp
 let A := equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c
 let B := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c)
 have hl : Nonempty (Derivation body (A :: Delta) (ReturnShape role typ tag)) := by
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨orLeft (Classical.choice (andLeft h))⟩
 have hr : Nonempty (Derivation body (B :: Delta) (ReturnShape role typ tag)) := by
  have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht := witnessTags H M W raw gamma c tag payload (andRight (andRight h)) (withHyp hp B)
  exact ⟨orRight (Classical.choice (andIntro (andLeft h) (andIntro (andLeft (andRight h)) ht)))⟩
 exact ⟨disjunctionElimination (Classical.choice ha)
   (Derivation.implicationIntroduction (Classical.choice hl))
   (Derivation.implicationIntroduction (Classical.choice hr))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
