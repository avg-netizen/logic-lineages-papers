module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsHeadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)
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

theorem headAccepted (H : Program 1) (M W : Program 2)
    (list entry tail gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (ha : Nonempty (Derivation body Delta (allGood H M W list gamma context))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) entry gamma context)) := by
  apply programCases ArgumentEntryCount.count ![tail,entry] _
  intro beta j Theta count hj hr
  simp only [graph3Rename,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ha' := renameInto ha j Theta hj
  rw [allGoodRename] at ha'
  have hv : (fun i => (![tail,entry] i).relabel j) = ![tail.relabel j,entry.relabel j] := by
    funext i; fin_cases i; rfl
  rw [hv] at hr
  have hl := ArgumentEntryCount.InternalProof.internalEqualCons body beta Theta
    (list.relabel j) (entry.relabel j) (tail.relabel j) (entry.relabel j) count hc' hr ⟨refl _⟩
  have hn : Nonempty (Derivation body Theta (eqn (suc count) z).not) := by
    exact ⟨Derivation.implicationIntroduction
      (sucNeZeroApply (Derivation.hypothesis List.mem_cons_self))⟩
  exact allGoodApply H M W (list.relabel j) (gamma.relabel j) (context.relabel j)
    (entry.relabel j) (suc count) ha' (andIntro hl hn)

theorem tailQuery (H : Program 1) (M W : Program 2)
    (list entry tail gamma context needle hits : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (ha : Nonempty (Derivation body Delta (allGood H M W list gamma context)))
    (hq : Nonempty (Derivation body Delta (query tail needle hits))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) needle gamma context)) := by
  apply formulaCases (eqn entry needle)
  · have hl := ArgumentEntryCount.InternalProof.internalEqualCons body alpha
      (eqn entry needle :: Delta) list entry tail needle hits (withHyp hc _)
      (andLeft (withHyp hq _)) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hn : Nonempty (Derivation body (eqn entry needle :: Delta) (eqn (suc hits) z).not) :=
      ⟨Derivation.implicationIntroduction
        (sucNeZeroApply (Derivation.hypothesis List.mem_cons_self))⟩
    exact allGoodApply H M W list gamma context needle (suc hits) (withHyp ha _) (andIntro hl hn)
  · have hl := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha
      ((eqn entry needle).not :: Delta) list entry tail needle hits (withHyp hc _)
      (andLeft (withHyp hq _)) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact allGoodApply H M W list gamma context needle hits (withHyp ha _)
      (andIntro hl (andRight (withHyp hq _)))

theorem tailAll (H : Program 1) (M W : Program 2)
    (list entry tail gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (ha : Nonempty (Derivation body Delta (allGood H M W list gamma context))) :
    Nonempty (Derivation body Delta (allGood H M W tail gamma context)) := by
  apply EntryFactsConstructorProof.allGoodIntro H M W tail gamma context
  intro beta j Theta needle hits hj hq
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ha' := renameInto ha j Theta hj
  rw [allGoodRename] at ha'
  exact tailQuery H M W (list.relabel j) (entry.relabel j) (tail.relabel j)
    (gamma.relabel j) (context.relabel j) needle hits hc' ha' hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsHeadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsHeadProof
