module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryProof
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

open EntryInductionDefinitions

theorem rawStep (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  apply EntryBindingProof.atRawIntro H raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 7) := raw.relabel Sum.inl
  let types : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let param : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let entries : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let entry : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let tau : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let child : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let Theta := fields H r types gamma param entries entry tau child :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result H r types gamma param entries entry tau child)
  have hf : Nonempty (Derivation body Theta (fields H r types gamma param entries entry tau child)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 7) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [EntryInductionSyntaxProof.belowRawRename] at ihj
  exact Classical.choice (EntryCoreProof.close H types r gamma param entries entry tau child (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf) ihj)

theorem allRaw (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  EntryBindingProof.rawInduction H raw (fun _ _ r ih => rawStep H r ih)

theorem typedEntry : Targets.InternalEntry := by
  intro body H alpha Delta types raw gamma param entries entry tau child ha hv hl ht
  exact EntryBindingProof.atRawApply H raw types gamma param entries entry tau child (allRaw H raw) (andIntro (andIntro (andIntro ha hv) hl) ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryProof
