module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleProof InternalBoundedCRTSyntaxProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTSupportProof InternalRelationalCRTStepProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof
open InternalLeastNumberSyntaxProof InternalTermSubstitutionSyntaxProof InternalBetaBoundaryProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
/-- Genuine PA induction, with all choices made by original existential elimination. -/
theorem actualRelationalCRT : InternalRelationalCRTTargets.ActualRelationalCRT := by
  intro body α n t R
  let T : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := t.relabel (Sum.map Sum.inl id)
  let Q : Formula (((α ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) := R.relabel (Sum.map (Sum.map Sum.inl id) id)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := ((InternalBoundedCRT.pairwiseBelow T x) ⊓ availableBelow Q x).imp (solution T Q x)
  have hb : Nonempty (Derivation body [] (instantiate theta (emb z))) := by
    simp only [theta,T,Q,x,impInstantiate,infInstantiate,pairwiseBelowInstantiate,
      availableBelowInstantiate,InternalRelationalCRTSyntaxProof.solutionInstantiate]
    obtain ⟨hz⟩ := solutionZero (body := body)
      (Gamma := [(InternalBoundedCRT.pairwiseBelow t z) ⊓ availableBelow R z]) t R
    exact ⟨Derivation.implicationIntroduction hz⟩
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    have hnext : successorInstance theta =
        ((InternalBoundedCRT.pairwiseBelow T (suc x)) ⊓ availableBelow Q (suc x)).imp (solution T Q (suc x)) := by
      simp only [theta,T,Q,x,successorInstance,nextEmbedding,impSubst,infSubst,
        pairwiseBelowSubst,availableBelowSubst,InternalRelationalCRTSyntaxProof.solutionSubst,
        termLiftNext,relationLiftNext,varNext]
    rw [hnext]
    let p := (InternalBoundedCRT.pairwiseBelow T (suc x)) ⊓ availableBelow Q (suc x)
    have hi : Derivation body (p :: [theta]) theta := Derivation.hypothesis (by simp)
    have hp : Derivation body (p :: [theta]) p := Derivation.hypothesis List.mem_cons_self
    obtain ⟨h⟩ := solutionStep T Q x ⟨hi⟩ ⟨Derivation.conjunctionLeft hp⟩ ⟨Derivation.conjunctionRight hp⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb n) (natInduction theta hb hs)
  simpa only [theta,T,Q,x,impInstantiate,infInstantiate,pairwiseBelowInstantiate,
    availableBelowInstantiate,InternalRelationalCRTSyntaxProof.solutionInstantiate] using
    (show Nonempty (Derivation body [] _) from ⟨h⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTProof
