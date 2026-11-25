module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (introduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel bindEmbedding nextEmbedding nextTerm varBind)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralRoundObserverTargets
open NumberedWindowInternalLiteralRoundObserverSyntaxProof
open NumberedWindowInternalLiteralRoundObserverCoreProof (stepCore baseCore)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

variable (E : Program 4) (O : Program 3)
private theorem zeroRow : Nonempty (Derivation body Delta (AtCount E O z)) := by
  apply introduction body alpha 7 Delta (matrix E O z)
  let vertices : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := inputs E O z vertices ctx ty seed out k m

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := baseCore E O vertices ctx ty seed out k m h
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem succRow (paid : Preserves E O)
    (elapsed : OTerm alpha) (row : Nonempty (Derivation body Delta (AtCount E O elapsed))) :
    Nonempty (Derivation body Delta (AtCount E O (suc elapsed))) := by
  apply introduction body alpha 7 Delta (matrix E O (suc elapsed))
  let vertices : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := inputs E O (suc (elapsed.relabel Sum.inl)) vertices ctx ty seed out k m

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have rr := renameInto row (Sum.inl : alpha → alpha ⊕ Fin 7)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at rr
  obtain ⟨step⟩ := stepCore E O paid (elapsed.relabel Sum.inl) vertices ctx ty seed out k m (withHyp rr A) ⟨h⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction step)

theorem allCounts (paid : Preserves E O)
    (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount E O count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount E O k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (zeroRow (body := body) (Delta := Delta) E O)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken) E O paid k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

/-- Independent of how any minimum is selected, every actual
occurrence of the original physical round has the observer's value.
The proof is object induction on the original fuel. -/
theorem exact_OpenRoundObserver (stable : Preserves E O) (fuel vertices ctx ty seed out k m : OTerm alpha)
    (held : Nonempty (Derivation body Delta (inputs E O fuel vertices ctx ty seed out k m))) :
    Nonempty (Derivation body Delta (observe O ctx ty k m)) :=
  applyAt E O fuel vertices ctx ty seed out k m (allCounts E O stable fuel) held

#print axioms exact_OpenRoundObserver
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInductionProof
