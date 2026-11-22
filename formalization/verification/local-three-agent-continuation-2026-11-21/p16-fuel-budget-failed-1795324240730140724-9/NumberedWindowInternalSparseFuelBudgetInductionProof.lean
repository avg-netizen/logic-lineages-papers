module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (introduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel bindEmbedding nextEmbedding nextTerm varBind)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFuelBudgetTargets
open NumberedWindowInternalSparseFuelBudgetSyntaxProof
open NumberedWindowInternalSparseFuelBudgetCoreProof (successorCore)
open NumberedWindowInternalSparseRoundExhaustionChecks (exact_InitialBudget)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private theorem zeroRow (E : Program 4) : Nonempty (Derivation body Delta (AtCount E z)) := by
  apply introduction body alpha 8 Delta
  let vertices : OTerm (alpha ⊕ Fin 8) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 8) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 8) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 8) := .var (.inr 3)
  let size : OTerm (alpha ⊕ Fin 8) := .var (.inr 4)
  let before : OTerm (alpha ⊕ Fin 8) := .var (.inr 5)
  let after : OTerm (alpha ⊕ Fin 8) := .var (.inr 6)
  let count : OTerm (alpha ⊕ Fin 8) := .var (.inr 7)
  let A := inputs E z vertices ctx ty seed size before after count

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨base⟩ := exact_InitialBudget body _ Γ vertices size before after count
  have d := Derivation.implicationElimination base (Derivation.conjunctionLeft h)
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem succRow (pred : ExactRetainedPredecessor) (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease)
    (E : Program 4) (elapsed : OTerm alpha) (row : Nonempty (Derivation body Delta (AtCount E elapsed))) :
    Nonempty (Derivation body Delta (AtCount E (suc elapsed))) := by
  apply introduction body alpha 8 Delta
  let vertices : OTerm (alpha ⊕ Fin 8) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 8) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 8) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 8) := .var (.inr 3)
  let size : OTerm (alpha ⊕ Fin 8) := .var (.inr 4)
  let before : OTerm (alpha ⊕ Fin 8) := .var (.inr 5)
  let after : OTerm (alpha ⊕ Fin 8) := .var (.inr 6)
  let count : OTerm (alpha ⊕ Fin 8) := .var (.inr 7)
  let A := inputs E (suc (elapsed.relabel Sum.inl)) vertices ctx ty seed size before after count

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have rr := renameInto row (Sum.inl : alpha → alpha ⊕ Fin 8)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at rr
  obtain ⟨step⟩ := successorCore pred strict E (elapsed.relabel Sum.inl) vertices ctx ty seed size before after count (withHyp rr A) ⟨h⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction step)

theorem allCounts (pred : ExactRetainedPredecessor) (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease)
    (E : Program 4) (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount E count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount E k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (zeroRow (body := body) (Delta := Delta) E)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken) pred strict E k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetInductionProof
