module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastInductionProof
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
open NumberedWindowInternalLiteralRoundLeastTargets
open NumberedWindowInternalLiteralRoundLeastSyntaxProof
open NumberedWindowInternalLiteralRoundLeastCoreProof (stepCore baseCore)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open NumberedWindowScalarAlgorithm (Settings)
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
private theorem zeroRow : Nonempty (Derivation body Delta (AtCount C X W s z)) := by
  apply introduction body alpha 7 Delta (matrix C X W s z)
  let vertices : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := inputs C X W s z vertices ctx ty seed out k m

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := baseCore C X W s vertices ctx ty seed out k m h
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction d)

private theorem succRow (paid : SameLeastOnEdge C X W s)
    (elapsed : OTerm alpha) (row : Nonempty (Derivation body Delta (AtCount C X W s elapsed))) :
    Nonempty (Derivation body Delta (AtCount C X W s (suc elapsed))) := by
  apply introduction body alpha 7 Delta (matrix C X W s (suc elapsed))
  let vertices : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let ctx : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let ty : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let seed : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let k : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let m : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := inputs C X W s (suc (elapsed.relabel Sum.inl)) vertices ctx ty seed out k m

  let Γ := A :: Delta.map (fun p => p.relabel Sum.inl)
  have h : Derivation body Γ A := Derivation.hypothesis List.mem_cons_self
  have rr := renameInto row (Sum.inl : alpha → alpha ⊕ Fin 7)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at rr
  obtain ⟨step⟩ := stepCore C X W s paid (elapsed.relabel Sum.inl) vertices ctx ty seed out k m (withHyp rr A) ⟨h⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction step)

theorem allCounts (paid : SameLeastOnEdge C X W s)
    (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount C X W s count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount C X W s k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (zeroRow (body := body) (Delta := Delta) C X W s)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken) C X W s paid k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastInductionProof
