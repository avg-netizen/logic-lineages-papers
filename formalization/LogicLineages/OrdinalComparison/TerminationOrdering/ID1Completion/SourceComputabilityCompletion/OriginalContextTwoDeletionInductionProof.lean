module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextTwoDeletionInductionSyntaxProof
open OriginalContextTwoDeletionBaseProof
open OriginalContextTwoDeletionCoreAssemblyProof
open OriginalAllPositionContextDeleteInductionCoreProof (contextNonzero)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (gamma count j a b upper lower left right : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields gamma count z j a b upper lower left right))) :
    Nonempty (Derivation body Delta (result z j a b upper lower left right)) := by
  apply nonzeroCases gamma _ (contextNonzero count gamma (suc j) (andLeft hf) (andLeft (andRight (andRight hf))))
  intro beta rho Theta head tail hrho hc
  simp only [resultRename,zRelabel]
  have hf' := renameInto hf rho Theta hrho
  simp only [fieldsRename,zRelabel] at hf'
  exact zeroKnownCons (gamma.relabel rho) head tail (upper.relabel rho) (lower.relabel rho)
    (left.relabel rho) (right.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) hc
    (andLeft (andRight (andRight (andRight (andRight (andRight hf'))))))
    (andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))
    (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))))
    (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))))
    (andLeft (andRight (andRight (andRight hf'))))
    (andLeft (andRight (andRight (andRight (andRight hf')))))


theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 9 Delta
  let gamma : OTerm (alpha ⊕ Fin 9) := .var (.inr 0)
  let count : OTerm (alpha ⊕ Fin 9) := .var (.inr 1)
  let j : OTerm (alpha ⊕ Fin 9) := .var (.inr 2)
  let a : OTerm (alpha ⊕ Fin 9) := .var (.inr 3)
  let b : OTerm (alpha ⊕ Fin 9) := .var (.inr 4)
  let upper : OTerm (alpha ⊕ Fin 9) := .var (.inr 5)
  let lower : OTerm (alpha ⊕ Fin 9) := .var (.inr 6)
  let left : OTerm (alpha ⊕ Fin 9) := .var (.inr 7)
  let right : OTerm (alpha ⊕ Fin 9) := .var (.inr 8)
  let A := fields gamma count z j a b upper lower left right
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 9))
  obtain ⟨h⟩ := zeroCore gamma count j a b upper lower left right (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (cutoff : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff))) :
    Nonempty (Derivation body Delta (row (suc cutoff))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 9 Delta
  let gamma : OTerm (alpha ⊕ Fin 9) := .var (.inr 0)
  let count : OTerm (alpha ⊕ Fin 9) := .var (.inr 1)
  let j : OTerm (alpha ⊕ Fin 9) := .var (.inr 2)
  let a : OTerm (alpha ⊕ Fin 9) := .var (.inr 3)
  let b : OTerm (alpha ⊕ Fin 9) := .var (.inr 4)
  let upper : OTerm (alpha ⊕ Fin 9) := .var (.inr 5)
  let lower : OTerm (alpha ⊕ Fin 9) := .var (.inr 6)
  let left : OTerm (alpha ⊕ Fin 9) := .var (.inr 7)
  let right : OTerm (alpha ⊕ Fin 9) := .var (.inr 8)
  let c := cutoff.relabel (Sum.inl : alpha → alpha ⊕ Fin 9)
  let A := fields gamma count (suc c) j a b upper lower left right
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 9))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore gamma count c j a b upper lower left right hrow' (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (cutoff : OTerm alpha) : Nonempty (Derivation body Delta (row cutoff)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb cutoff) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualContextSquare : OriginalContextTwoDeletionTargets.ActualContextSquare := by
  intro body alpha Delta gamma count i j a b upper lower left right
  let A := fields gamma count i j a b upper lower left right
  obtain ⟨h⟩ := rowApply gamma count i j a b upper lower left right
    (allRows (body := body) (Delta := A :: Delta) i)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionProof
