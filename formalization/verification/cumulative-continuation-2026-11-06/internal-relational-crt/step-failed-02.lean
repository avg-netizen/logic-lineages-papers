module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalCoprimeMultipleSupportProof InternalCoprimeMultipleStepProof InternalCoprimeMultipleProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof InternalRelationalCRTSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof
open InternalBezoutExistenceTargets InternalDivisibilityProof InternalModularArithmeticProof InternalOriginalOrderProof
open InternalGraphCompositionSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem combineSolution (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n c p s : OTerm α)
    (hR : Nonempty (Derivation body Gamma (instantiate (atIndex R n) (emb s))))
    (hc : Nonempty (Derivation body Gamma (coprime (suc (t.subst (bindTerm n))) (suc p))))
    (hd : Nonempty (Derivation body Gamma (dividesBelow t (suc p) n)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t R c n))) :
    Nonempty (Derivation body Gamma (solution t R (suc n))) := by
  obtain ⟨hb⟩ := InternalBinaryCRTProof.actualBinaryCRT body α (t.subst (bindTerm n)) p s c
  obtain ⟨hc⟩ := hc
  have hb := Derivation.implicationElimination (weakenClosed hb Gamma) hc
  apply InternalBoundedCRTSyntaxProof.binarySolutionCases Gamma _ _ _ _ _ ⟨hb⟩
  intro β j Delta d hj hn hdc
  rw [solutionRename,sucRelabel]
  have hd' := renameInto hd j Delta hj
  rw [dividesBelowRename] at hd'
  have hr' := renameInto hr j Delta hj
  rw [residuesBelowRename] at hr'
  have hR' := renameInto hR j Delta hj
  rw [instantiateRename,← onTermRelabel,atIndexRename] at hR'
  apply solutionIntroduction _ _ _ d
  apply boundedStep _ (n.relabel j)
    (preserveResidues _ _ _ _ _ _ hd' hdc hr')
  rw [chosenInstantiate,liftBind,sucSubst]
  apply chosenIntroduction _ _ _ (s.relabel j) hR'
  simpa only [sucRelabel,familyEvaluationRename] using hn

theorem extendWitness (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n c s : OTerm α)
    (hR : Nonempty (Derivation body Gamma (instantiate (atIndex R n) (emb s))))
    (hn : Nonempty (Derivation body Gamma (coprimeBelow (suc (t.subst (bindTerm n))) t n)))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t R c n))) :
    Nonempty (Derivation body Gamma (solution t R (suc n))) := by
  obtain ⟨hm⟩ := actualBoundedCoprimeMultiple body α (t.subst (bindTerm n)) n t
  obtain ⟨hn⟩ := hn
  have hm := Derivation.implicationElimination (weakenClosed hm Gamma) hn
  apply commonCases Gamma _ t n _ ⟨hm⟩
  intro β j Delta p hj hc hd
  rw [solutionRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [residuesBelowRename] at hr'
  have hR' := renameInto hR j Delta hj
  rw [instantiateRename,← onTermRelabel,atIndexRename] at hR'
  simp only [sucRelabel,familyEvaluationRename] at hc
  exact combineSolution _ _ _ _ p (s.relabel j) hR' hc hd hr'

theorem extendSolution (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n c : OTerm α)
    (hn : Nonempty (Derivation body Gamma (coprimeBelow (suc (t.subst (bindTerm n))) t n)))
    (hav : Nonempty (Derivation body Gamma (existsOne (atIndex R n))))
    (hr : Nonempty (Derivation body Gamma (residuesBelow t R c n))) :
    Nonempty (Derivation body Gamma (solution t R (suc n))) := by
  apply existsCases Gamma (atIndex R n) _ hav
  intro β j Delta s hj hR
  rw [solutionRename,sucRelabel]
  have hr' := renameInto hr j Delta hj
  rw [residuesBelowRename] at hr'
  have hn' := renameInto hn j Delta hj
  rw [coprimeBelowRename,sucRelabel,familyEvaluationRename] at hn'
  rw [atIndexRename] at hR
  exact extendWitness _ _ _ _ s hR hn' hr'

theorem solutionStep (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α)
    (hi : Nonempty (Derivation body Gamma (((InternalBoundedCRT.pairwiseBelow t n) ⊓ availableBelow R n).imp
      (solution t R n))))
    (ha : Nonempty (Derivation body Gamma (InternalBoundedCRT.pairwiseBelow t (suc n))))
    (hav : Nonempty (Derivation body Gamma (availableBelow R (suc n)))) :
    Nonempty (Derivation body Gamma (solution t R (suc n))) := by
  obtain ⟨ha'⟩ := boundedRestrict _ n ha
  obtain ⟨hav'⟩ := boundedRestrict _ n hav
  obtain ⟨hi⟩ := hi
  have hs := Derivation.implicationElimination hi (Derivation.conjunctionIntroduction ha' hav')
  have hn := InternalBoundedCRTSupportProof.pairwiseLast t n ha
  have hnew := availableLast R n hav
  apply solutionCases Gamma t R n _ ⟨hs⟩
  intro β j Delta c hj hr
  rw [solutionRename,sucRelabel]
  have hn' := renameInto hn j Delta hj
  rw [coprimeBelowRename,sucRelabel,familyEvaluationRename] at hn'
  have hnew' := renameInto hnew j Delta hj
  rw [existsRename,atIndexRename] at hnew'
  exact extendSolution _ _ _ c hn' hnew' hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTStepProof
