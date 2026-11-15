module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BoundProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalAdditionLawsProof (leftZero)
open Continuation20261114
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)

open CoreProof SupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (bindEmbedding varBind nextTerm nextEmbedding)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem rowZero (n : Nat) :
    Nonempty (Derivation body Delta (AtCount n z)) := by
  apply introduction body alpha 6 Delta
  let seed : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let seedRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let childRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields n z seed param frontier child seedRank childRank
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have hA : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := Theta) n seed param frontier child seedRank childRank
    (andLeft (andLeft hA)) (andRight (andLeft hA)) (andLeft (andRight hA)) (andRight (andRight hA))
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem rowSuccessor (n : Nat) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount n count))) :
    Nonempty (Derivation body Delta (AtCount n (suc count))) := by
  apply introduction body alpha 6 Delta
  let seed : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let seedRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let childRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields n (suc (count.relabel Sum.inl)) seed param frontier child seedRank childRank
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have hA : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr := InternalGraphCompositionFunctionalityProof.renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 6)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  obtain ⟨h⟩ := successorCore (body := body) (Delta := Theta) n (count.relabel Sum.inl) seed param frontier child seedRank childRank
    (withHyp hr A)
    (andLeft (andLeft hA)) (andRight (andLeft hA)) (andLeft (andRight hA)) (andRight (andRight hA))
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem allCounts (n : Nat) (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount n count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount n k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (rowZero (body := body) (Delta := Delta) n)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := rowSuccessor (body := body) (Delta := theta :: Delta.map weaken) n k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

theorem rankBound : Targets.InternalRankBound := by
  intro n body alpha Delta depth seed param frontier child seedRank childRank hr hf hm hc
  exact rowApply n depth seed param frontier child seedRank childRank (allCounts n depth) hr hf hm hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.BoundProof
