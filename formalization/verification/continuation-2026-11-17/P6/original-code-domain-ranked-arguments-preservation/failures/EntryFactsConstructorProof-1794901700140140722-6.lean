module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalSourceIntroductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open EntryFacts EntryFactsSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilQuery (H : Program 1) (M W : Program 2) (gamma context needle hits : OTerm alpha)
    (hq : Nonempty (Derivation body Delta (query z needle hits))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) needle gamma context)) := by
  obtain ⟨he⟩ := valueUnique ArgumentEntryCount.count hits z ![z,needle] (andLeft hq)
    (ArgumentEntryCount.InternalProof.internalNil body alpha Delta needle)
  obtain ⟨hn⟩ := andRight hq
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn he)⟩

theorem consQuery (H : Program 1) (M W : Program 2)
    (list entry tail gamma context needle hits : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (hh : Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) entry gamma context)))
    (ht : Nonempty (Derivation body Delta (allGood H M W tail gamma context)))
    (hq : Nonempty (Derivation body Delta (query list needle hits))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) needle gamma context)) := by
  apply formulaCases (eqn entry needle)
  · exact headTransport (entryCheck H M W) (suc z) entry needle ![gamma,context]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hh (eqn entry needle))
  · let A := (eqn entry needle).not
    have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply programCases ArgumentEntryCount.count ![tail,needle] _
    intro beta j Theta count hj hr
    simp only [graph3Rename,sucRelabel,zRelabel]
    have hn' := renameInto hn j Theta hj
    simp only [OriginalTypedDecoderTransportLogicalProof.notRename,eqnRelabel] at hn'
    have hc' := renameInto (withHyp hc A) j Theta hj
    rw [graph2Rename] at hc'
    have ht' := renameInto (withHyp ht A) j Theta hj
    rw [allGoodRename] at ht'
    have hq' := renameInto (withHyp hq A) j Theta hj
    rw [queryRename] at hq'
    have hv : (fun i => (![tail,needle] i).relabel j) = ![tail.relabel j,needle.relabel j] := by
      funext i; fin_cases i; rfl
    rw [hv] at hr
    have hl := ArgumentEntryCount.InternalProof.internalUnequalCons body beta Theta
      (list.relabel j) (entry.relabel j) (tail.relabel j) (needle.relabel j) count hc' hr hn'
    have he := valueUnique ArgumentEntryCount.count count (hits.relabel j)
      ![list.relabel j,needle.relabel j] hl (andLeft hq')
    have hr' := outputTransport ArgumentEntryCount.count count (hits.relabel j)
      ![tail.relabel j,needle.relabel j] he hr
    exact allGoodApply H M W (tail.relabel j) (gamma.relabel j) (context.relabel j)
      (needle.relabel j) (hits.relabel j) ht' (andIntro hr' (andRight hq'))
/-- Introduce the actual finite universal query block without changing its matrix. -/
theorem allGoodIntro (H : Program 1) (M W : Program 2) (list gamma context : OTerm alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (needle hits : OTerm beta), (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (query (list.relabel j) needle hits)) →
      Nonempty (Derivation body Theta (graph3 (entryCheck H M W) (suc z) needle
        (gamma.relabel j) (context.relabel j)))) :
    Nonempty (Derivation body Delta (allGood H M W list gamma context)) := by
  unfold allGood
  apply InternalClosedProgramsBindingProof.introduction body alpha 2 Delta
  let needle : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let hits : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := query (list.relabel Sum.inl) needle hits
  let Theta := A :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  obtain ⟨h⟩ := next (alpha ⊕ Fin 2) Sum.inl Theta needle hits
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem nilAll (H : Program 1) (M W : Program 2) (gamma context : OTerm alpha) :
    Nonempty (Derivation body Delta (allGood H M W z gamma context)) := by
  apply allGoodIntro H M W z gamma context
  intro beta j Theta needle hits hj hq
  simp only [zRelabel] at hq
  exact nilQuery H M W (gamma.relabel j) (context.relabel j) needle hits hq

theorem consAll (H : Program 1) (M W : Program 2)
    (list entry tail gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (hh : Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) entry gamma context)))
    (ht : Nonempty (Derivation body Delta (allGood H M W tail gamma context))) :
    Nonempty (Derivation body Delta (allGood H M W list gamma context)) := by
  apply allGoodIntro H M W list gamma context
  intro beta j Theta needle hits hj hq
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hh' := renameInto hh j Theta hj
  simp only [graph3Rename,sucRelabel,zRelabel] at hh'
  have ht' := renameInto ht j Theta hj
  rw [allGoodRename] at ht'
  exact consQuery H M W (list.relabel j) (entry.relabel j) (tail.relabel j)
    (gamma.relabel j) (context.relabel j) needle hits hc' hh' ht' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsConstructorProof
