module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalLinearCombinationSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalLeastNumberSyntaxProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalCoprimeMultipleSupportProof InternalDivisibilityProductProof InternalProductCoprimalityProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof
open InternalBezoutExistenceTargets InternalDivisibilityProof InternalTermSubstitutionSyntaxProof
open InternalBetaDivisionSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem boundedDividesProduct (t : OTerm (α ⊕ Fin 1)) (P B n : OTerm α)
    (h : Nonempty (Derivation body Gamma (dividesBelow t P n))) :
    Nonempty (Derivation body Gamma (dividesBelow t (mul P B) n)) := by
  unfold dividesBelow at h ⊢
  apply boundedMap _ _ n h
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  simp only [mulRelabel]
  obtain ⟨hd⟩ := dividesProduct (suc t) (P.relabel Sum.inl) (B.relabel Sum.inl)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact hd

theorem extendMultiple (m : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n p : OTerm α)
    (hc : Nonempty (Derivation body Gamma (coprime (suc m) (suc p))))
    (hd : Nonempty (Derivation body Gamma (dividesBelow t (suc p) n)))
    (hn : Nonempty (Derivation body Gamma (coprime (suc m) (suc (t.subst (bindTerm n)))))) :
    Nonempty (Derivation body Gamma (commonMultiple (suc m) t (suc n))) := by
  let b := t.subst (bindTerm n)
  let P := mul (suc p) (suc b)
  let r := add (mul p (suc b)) b
  obtain ⟨cp⟩ := positiveProductCoprimality m p b hc hn
  have hh := boundedDividesProduct t (suc p) (suc b) n hd
  have he : Nonempty (Derivation body Gamma (instantiate
      (arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc t) (P.relabel Sum.inl))) (emb n))) := by
    rw [instantiate,bindEmbedding,dividesSubst,sucSubst,liftBind]
    exact dividesRightProduct (suc p) (suc b)
  obtain ⟨hP⟩ := boundedStep _ n hh he
  have hp : Derivation body Gamma (eqn P (suc r)) := positiveProduct p b
  exact commonIntroduction (suc m) t (suc n) r
    ⟨coprimeCongruence (suc m) P (suc r) hp cp⟩
    ⟨dividesBelowCongruence t P (suc r) (suc n) hp hP⟩

theorem familyEvaluationRename {α β : Type} (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (t.subst (bindTerm n)).relabel j =
      (t.relabel (Sum.map j id)).subst (bindTerm (n.relabel j)) := by
  rw [termSubstRelabel,termRelabelSubst]
  congr 1
  funext x
  cases x <;> rfl

theorem multipleStep (m : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n : OTerm α)
    (hi : Nonempty (Derivation body Gamma ((coprimeBelow (suc m) t n).imp (commonMultiple (suc m) t n))))
    (ha : Nonempty (Derivation body Gamma (coprimeBelow (suc m) t (suc n)))) :
    Nonempty (Derivation body Gamma (commonMultiple (suc m) t (suc n))) := by
  obtain ⟨ha'⟩ := boundedRestrict _ n ha
  obtain ⟨hi⟩ := hi
  have hm := Derivation.implicationElimination hi ha'
  obtain ⟨ha⟩ := ha
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Gamma) n
  have hn := boundedElim _ n (suc n) ha hn
  rw [coprimeInstantiate,liftBind,sucSubst] at hn
  apply commonCases Gamma (suc m) t n _ ⟨hm⟩
  intro β j Delta p hj hc hd
  rw [commonMultipleRename,sucRelabel,sucRelabel]
  have hn' := renameInto ⟨hn⟩ j Delta hj
  rw [coprimeRename,sucRelabel,sucRelabel,familyEvaluationRename] at hn'
  simp only [sucRelabel] at hc
  exact extendMultiple (m.relabel j) (t.relabel (Sum.map j id)) (n.relabel j) p hc hd hn'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleStepProof
