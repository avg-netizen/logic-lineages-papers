module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BoundProof
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
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)

open CoreProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (bindEmbedding varBind nextTerm nextEmbedding)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem rowZero : Nonempty (Derivation body Delta (AtCount z)) := by
  apply introduction body alpha 4 Delta
  let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields z seed param frontier child
  obtain ⟨h⟩ := zeroCore (body := body)
    (Delta := A :: Delta.map (fun p => p.relabel Sum.inl)) seed param frontier child
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem rowSuccessor (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount count))) :
    Nonempty (Derivation body Delta (AtCount (suc count))) := by
  apply introduction body alpha 4 Delta
  let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields (suc (count.relabel Sum.inl)) seed param frontier child
  have hr := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 4)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  obtain ⟨h⟩ := successorCore (count.relabel Sum.inl) seed param frontier child
    (withHyp hr A) ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem allCounts (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (rowZero (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := rowSuccessor (body := body) (Delta := theta :: Delta.map weaken) k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h


theorem rankBound : Targets.InternalRankBound := by
  intro body alpha Delta depth seed param frontier child hf hm
  exact rowApply depth seed param frontier child (allCounts depth) hf hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BoundProof
