module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalCoprimeMultipleSupportProof InternalCoprimeMultipleStepProof InternalCoprimeMultipleProof
open InternalBoundedCRT InternalBoundedCRTSyntaxProof InternalBoundedCRTSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalBinaryCRTSyntaxProof InternalDerivationRenamingSyntaxProof InternalOriginalOrderProof
open InternalBezoutExistenceTargets InternalDivisibilityProof InternalModularArithmeticProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem combineSolution (t r : OTerm (α ⊕ Fin 1)) (n c p : OTerm α)
    (hc : Nonempty (Derivation body Gamma (coprime (suc (t.subst (bindTerm n))) (suc p))))
    (hd : Nonempty (Derivation body Gamma (dividesBelow t (suc p) n)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t r c n))) :
    Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r (suc n))) := by
  obtain ⟨hb⟩ := InternalBinaryCRTProof.actualBinaryCRT body α (t.subst (bindTerm n)) p
    (r.subst (bindTerm n)) c
  obtain ⟨hc⟩ := hc
  have hb := Derivation.implicationElimination (weakenClosed hb Gamma) hc
  apply binarySolutionCases Gamma _ _ _ _ _ ⟨hb⟩
  intro β j Delta d hj hn hdc
  rw [InternalBoundedCRTSyntaxProof.solutionRename,sucRelabel]
  have hd' := renameInto hd j Delta hj
  rw [dividesBelowRename] at hd'
  have hr' := renameInto hr j Delta hj
  rw [residuesBelowRename] at hr'
  apply InternalBoundedCRTSyntaxProof.solutionIntroduction _ _ _ d
  apply boundedStep _ (n.relabel j)
    (preserveResidues _ _ _ _ _ _ hd' hdc hr')
  rw [congruentInstantiate,liftBind,sucSubst]
  simpa only [sucRelabel,familyEvaluationRename] using hn

theorem extendSolution (t r : OTerm (α ⊕ Fin 1)) (n c : OTerm α)
    (hn : Nonempty (Derivation body Gamma (coprimeBelow (suc (t.subst (bindTerm n))) t n)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t r c n))) :
    Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r (suc n))) := by
  obtain ⟨hm⟩ := actualBoundedCoprimeMultiple body α (t.subst (bindTerm n)) n t
  obtain ⟨hn⟩ := hn
  have hm := Derivation.implicationElimination (weakenClosed hm Gamma) hn
  apply commonCases Gamma _ t n _ ⟨hm⟩
  intro β j Delta p hj hc hd
  rw [InternalBoundedCRTSyntaxProof.solutionRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [residuesBelowRename] at hr'
  simp only [sucRelabel,familyEvaluationRename] at hc
  exact combineSolution _ _ _ _ p hc hd hr'

theorem solutionStep (t r : OTerm (α ⊕ Fin 1)) (n : OTerm α)
    (hi : Nonempty (Derivation body Gamma ((pairwiseBelow t n).imp (InternalBoundedCRT.solution t r n))))
    (ha : Nonempty (Derivation body Gamma (pairwiseBelow t (suc n)))) :
    Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r (suc n))) := by
  obtain ⟨ha'⟩ := boundedRestrict _ n ha
  obtain ⟨hi⟩ := hi
  have hs := Derivation.implicationElimination hi ha'
  have hn := pairwiseLast t n ha
  apply solutionCases Gamma t r n _ ⟨hs⟩
  intro β j Delta c hj hr
  rw [InternalBoundedCRTSyntaxProof.solutionRename,sucRelabel]
  have hn' := renameInto hn j Delta hj
  rw [coprimeBelowRename,sucRelabel,familyEvaluationRename] at hn'
  exact extendSolution _ _ _ c hn' hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTStepProof
