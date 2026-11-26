module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.Proof
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

open InductionDefinitions

theorem rawStep (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  apply BindingProof.atRawIntro H raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 4) := raw.relabel Sum.inl
  let types : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let param : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let Theta := fields H r types gamma param value :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result H r types gamma param value)
  have hf : Nonempty (Derivation body Theta (fields H r types gamma param value)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 4) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact Classical.choice (CoreProof.close H types r gamma param value (andLeft hf) (andRight hf) ihj)

theorem allRaw (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  BindingProof.rawInduction H raw (fun _ _ r ih => rawStep H r ih)

theorem typedDefined : Targets.InternalTypedDefined := by
  intro body H alpha Delta types raw gamma param value ha hv
  exact BindingProof.atRawApply H raw types gamma param value (allRaw H raw) (andIntro ha hv)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesDefined.Proof
