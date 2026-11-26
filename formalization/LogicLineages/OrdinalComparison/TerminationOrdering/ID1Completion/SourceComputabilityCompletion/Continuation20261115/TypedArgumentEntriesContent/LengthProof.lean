module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)

open LengthInductionDefinitions

theorem rawStep (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  apply LengthBindingProof.atRawIntro H raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 6) := raw.relabel Sum.inl
  let types : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let param : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let entries : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let entryLength : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let typeLength : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let Theta := fields H r types gamma param entries entryLength typeLength :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result H r types gamma param entries entryLength typeLength)
  have hf : Nonempty (Derivation body Theta (fields H r types gamma param entries entryLength typeLength)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 6) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [LengthInductionSyntaxProof.belowRawRename] at ihj
  exact Classical.choice (LengthCoreProof.close H types r gamma param entries entryLength typeLength (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf) ihj)

theorem allRaw (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  LengthBindingProof.rawInduction H raw (fun _ _ r ih => rawStep H r ih)

theorem typedLength : Targets.InternalLength := by
  intro body H alpha Delta types raw gamma param entries entryLength typeLength ha hv hl ht
  exact LengthBindingProof.atRawApply H raw types gamma param entries entryLength typeLength (allRaw H raw) (andIntro (andIntro (andIntro ha hv) hl) ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.LengthProof
