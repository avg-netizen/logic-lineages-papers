module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.Proof
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

open OriginalContextInsertion (lengthGraph)

open OriginalContextInsertion (Below)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalOriginalOrderSyntaxProof (orderRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open InductionDefinitions

theorem rawStep (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  apply BindingProof.atRawIntro H raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 10) := raw.relabel Sum.inl
  let types : OTerm (alpha ⊕ Fin 10) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 10) := .var (.inr 1)
  let param : OTerm (alpha ⊕ Fin 10) := .var (.inr 2)
  let entries : OTerm (alpha ⊕ Fin 10) := .var (.inr 3)
  let count : OTerm (alpha ⊕ Fin 10) := .var (.inr 4)
  let index : OTerm (alpha ⊕ Fin 10) := .var (.inr 5)
  let entry : OTerm (alpha ⊕ Fin 10) := .var (.inr 6)
  let annotation : OTerm (alpha ⊕ Fin 10) := .var (.inr 7)
  let child : OTerm (alpha ⊕ Fin 10) := .var (.inr 8)
  let expected : OTerm (alpha ⊕ Fin 10) := .var (.inr 9)
  let Theta := fields H r types gamma param entries count index entry annotation child expected :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result H r types gamma param entries count index entry annotation child expected)
  have hf : Nonempty (Derivation body Theta (fields H r types gamma param entries count index entry annotation child expected)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 10) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact Classical.choice (CoreProof.close H types r gamma param entries count index entry annotation child expected (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))) (andRight (andLeft (andLeft (andLeft (andLeft hf))))) (andRight (andLeft (andLeft (andLeft hf)))) (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf) ihj)

theorem allRaw (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H raw)) :=
  BindingProof.rawInduction H raw (fun _ _ r ih => rawStep H r ih)

theorem typedPosition : Targets.InternalPosition := by
  intro body H alpha Delta types raw gamma param entries count index entry annotation child expected ha hv hl hb hlook htlook hq
  exact BindingProof.atRawApply H raw types gamma param entries count index entry annotation child expected (allRaw H raw) (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro ha hv) hl) hb) hlook) htlook) hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesPosition.Proof
