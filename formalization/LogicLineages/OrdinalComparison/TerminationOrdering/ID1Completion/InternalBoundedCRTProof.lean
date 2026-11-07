module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleProof
open InternalBoundedCRT InternalBoundedCRTSyntaxProof InternalBoundedCRTSupportProof InternalBoundedCRTStepProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof
open InternalLeastNumberSyntaxProof InternalTermSubstitutionSyntaxProof InternalBetaBoundaryProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
/-- PA induction is performed on the fresh object variable, uniformly in all
    original parameters, modulus terms, residue terms, and the final bound. -/
theorem actualBoundedCRT : InternalBoundedCRTTargets.ActualBoundedCRT := by
  intro body α n t r
  let T : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := t.relabel (Sum.map Sum.inl id)
  let R : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := r.relabel (Sum.map Sum.inl id)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := (pairwiseBelow T x).imp (InternalBoundedCRT.solution T R x)
  have hb : Nonempty (Derivation body [] (instantiate theta (emb z))) := by
    simp only [theta,T,R,x,impInstantiate,pairwiseBelowInstantiate,solutionInstantiate]
    obtain ⟨hz⟩ := solutionZero (body := body) (Gamma := [pairwiseBelow t z]) t r
    exact ⟨Derivation.implicationIntroduction hz⟩
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    have hnext : successorInstance theta =
        (pairwiseBelow T (suc x)).imp (InternalBoundedCRT.solution T R (suc x)) := by
      simp only [theta,T,R,x,successorInstance,nextEmbedding,impSubst,
        pairwiseBelowSubst,solutionSubst,termLiftNext,varNext]
    rw [hnext]
    have hi : Derivation body (pairwiseBelow T (suc x) :: [theta]) theta :=
      Derivation.hypothesis (by simp)
    have ha : Derivation body (pairwiseBelow T (suc x) :: [theta]) (pairwiseBelow T (suc x)) :=
      Derivation.hypothesis List.mem_cons_self
    obtain ⟨h⟩ := solutionStep T R x ⟨hi⟩ ⟨ha⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb n) (natInduction theta hb hs)
  simpa only [theta,T,R,x,impInstantiate,pairwiseBelowInstantiate,solutionInstantiate] using
    (show Nonempty (Derivation body [] _) from ⟨h⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTProof
