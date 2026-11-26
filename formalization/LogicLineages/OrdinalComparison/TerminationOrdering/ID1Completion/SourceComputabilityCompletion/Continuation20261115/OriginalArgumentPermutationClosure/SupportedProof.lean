module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SupportedInductionDefinitions SupportedInductionSyntaxProof SupportedBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 5) := raw.relabel Sum.inl
  let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let needle : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let lc : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let rc : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let Theta := fields r left right needle lc rc :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r left right needle lc rc)
  have hf : Nonempty (Derivation body Theta (fields r left right needle lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 5) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  exact Classical.choice (SupportedCoreProof.core r left right needle lc rc (andLeft (andLeft (andLeft hf))) (andRight (andLeft (andLeft hf))) (andRight (andLeft hf)) (andRight hf) ihj)

theorem supportedCounts (raw left right needle lc rc : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle)))
    : Nonempty (Derivation body Delta (eqn lc rc)) := by
  exact atRawApply raw left right needle lc rc (rawInduction raw (fun _ _ r h => rawStep r h))
    (andIntro (andIntro (andIntro ha hm) hl) hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedProof
