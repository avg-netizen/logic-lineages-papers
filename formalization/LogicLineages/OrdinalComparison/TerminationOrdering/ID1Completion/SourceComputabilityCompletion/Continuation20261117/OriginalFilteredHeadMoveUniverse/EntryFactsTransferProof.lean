module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalSourceIntroductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open Continuation20261115.OriginalArgumentPermutationClosure
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof
open EntryFacts EntryFactsSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem transferQuery (H : Program 1) (M W : Program 2)
    (left right gamma context needle hits : OTerm alpha)
    (he : Nonempty (Derivation body Delta (agreement left right)))
    (ha : Nonempty (Derivation body Delta (allGood H M W left gamma context)))
    (hq : Nonempty (Derivation body Delta (query right needle hits))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) needle gamma context)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons left (Fin.cons needle Fin.elim0)) _
  intro beta j Theta count hj hc
  simp only [graph3Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hc
  have he' := renameInto he j Theta hj
  rw [agreementRename] at he'
  have ha' := renameInto ha j Theta hj
  rw [allGoodRename] at ha'
  have hq' := renameInto hq j Theta hj
  rw [queryRename] at hq'
  have heq := agreementApply (left.relabel j) (right.relabel j) (needle.relabel j) count (hits.relabel j)
    he' hc (andLeft hq')
  have hc' := outputTransport ArgumentEntryCount.count count (hits.relabel j)
    ![left.relabel j,needle.relabel j] heq hc
  exact allGoodApply H M W (left.relabel j) (gamma.relabel j) (context.relabel j)
    (needle.relabel j) (hits.relabel j) ha' (andIntro hc' (andRight hq'))

theorem transferAll (H : Program 1) (M W : Program 2)
    (left right gamma context : OTerm alpha)
    (he : Nonempty (Derivation body Delta (agreement left right)))
    (ha : Nonempty (Derivation body Delta (allGood H M W left gamma context))) :
    Nonempty (Derivation body Delta (allGood H M W right gamma context)) := by
  unfold allGood
  apply InternalClosedProgramsBindingProof.introduction body alpha 2 Delta
  let needle : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let hits : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := query (right.relabel Sum.inl) needle hits
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have he' := renameInto he Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [agreementRename] at he'
  have ha' := renameInto ha Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [allGoodRename] at ha'
  obtain ⟨h⟩ := transferQuery H M W (left.relabel Sum.inl) (right.relabel Sum.inl)
    (gamma.relabel Sum.inl) (context.relabel Sum.inl) needle hits he' ha'
    (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsTransferProof
