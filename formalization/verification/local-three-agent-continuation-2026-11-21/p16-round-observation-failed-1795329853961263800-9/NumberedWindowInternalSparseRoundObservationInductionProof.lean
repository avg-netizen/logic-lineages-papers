module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationInductionProof
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
open NumberedWindowInternalSparseRoundObservationTargets
open NumberedWindowInternalSparseRoundObservationSyntaxProof
open NumberedWindowInternalSparseRoundObservationCoreProof (stepCore baseCore)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


open NumberedWindowScalarAlgorithm (Settings)
variable (E : Program 4) (M : Program 5)
private theorem zeroRow : Nonempty (Derivation body Delta (AtCount E M z)) := by
  apply introduction body alpha 10 Delta (matrix E M z)
  let vertices : OTerm (alpha ⊕ Fin 10) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 10) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 10) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 10) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 10) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 10) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 10) := .var (.inr 6)
  let dom : OTerm (alpha ⊕ Fin 10) := .var (.inr 7)
  let cod : OTerm (alpha ⊕ Fin 10) := .var (.inr 8)
  let arg : OTerm (alpha ⊕ Fin 10) := .var (.inr 9)
  let A := inputs E M z vertices ctx ty seed out k m dom cod arg

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := baseCore E M vertices ctx ty seed out k m dom cod arg h
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem succRow 
    (elapsed : OTerm alpha) (row : Nonempty (Derivation body Delta (AtCount E M elapsed))) :
    Nonempty (Derivation body Delta (AtCount E M (suc elapsed))) := by
  apply introduction body alpha 10 Delta (matrix E M (suc elapsed))
  let vertices : OTerm (alpha ⊕ Fin 10) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 10) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 10) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 10) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 10) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 10) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 10) := .var (.inr 6)
  let dom : OTerm (alpha ⊕ Fin 10) := .var (.inr 7)
  let cod : OTerm (alpha ⊕ Fin 10) := .var (.inr 8)
  let arg : OTerm (alpha ⊕ Fin 10) := .var (.inr 9)
  let A := inputs E M (suc (elapsed.relabel Sum.inl)) vertices ctx ty seed out k m dom cod arg

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have rr := renameInto row (Sum.inl : alpha → alpha ⊕ Fin 10)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at rr
  obtain ⟨step⟩ := stepCore E M (elapsed.relabel Sum.inl) vertices ctx ty seed out k m dom cod arg (withHyp rr A) ⟨h⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction step)

theorem allCounts 
    (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount E M count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount E M k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (zeroRow (body := body) (Delta := Delta) E M)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken) E M k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationInductionProof
