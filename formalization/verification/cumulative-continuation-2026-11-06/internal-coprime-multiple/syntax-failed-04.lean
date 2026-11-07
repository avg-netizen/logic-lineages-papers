module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalLinearCombinationSyntaxProof
open InternalOriginalOrderSyntaxProof InternalLeastNumberSyntaxProof InternalCoprimeMultiple
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof InternalDerivationRenamingSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalBezoutExistenceTargets InternalDivisibilityProof
open InternalGraphCompositionSyntaxProof InternalQuotientComparisonSyntaxProof

theorem infSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊓ q).subst ts = p.subst ts ⊓ q.subst ts := rfl
theorem infInstantiate {α : Type} (p q : Formula (α ⊕ Fin 1)) (s : Term α) :
    instantiate (p ⊓ q) s = instantiate p s ⊓ instantiate q s := rfl

theorem mapInl {α β : Type} (j : α → β) :
    (Sum.map j id : α ⊕ Fin 1 → β ⊕ Fin 1) ∘ Sum.inl = Sum.inl ∘ j := by
  funext x; rfl
theorem varMap {α β : Type} (j : α → β) (i : Fin 1) :
    (Term.relabel (Sum.map j id) (.var (.inr i)) : OTerm (β ⊕ Fin 1)) = .var (.inr i) := rfl


theorem liftEmbedding {α β : Type} (ts : α → OTerm β) :
    Sum.elim (fun a => (emb (ts a)).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i)) =
      (fun a => emb (liftTerms ts a)) := by
  funext a
  cases a with
  | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
  | inr i => rfl

theorem liftSubst {α β : Type} (t : OTerm α) (ts : α → OTerm β) :
    (t.relabel Sum.inl).subst (liftTerms ts) = (t.subst ts).relabel Sum.inl := by
  rw [termRelabelSubst,termSubstRelabel]; rfl

theorem dividesSubst {α β : Type} (d a : OTerm α) (ts : α → OTerm β) :
    (arithmeticEmbedding.onFormula (InternalLinearCombination.divides d a)).subst (fun x => emb (ts x)) =
      arithmeticEmbedding.onFormula (InternalLinearCombination.divides (d.subst ts) (a.subst ts)) := by
  rw [← embedSubst]
  unfold InternalLinearCombination.divides
  rw [existsFinSubst,equalitySubstitution]
  congr 1
  simp only [mulSubst]
  change ((a.relabel Sum.inl).subst (liftTerms ts)).equal
    (mul (.var (.inr 0)) ((d.relabel Sum.inl).subst (liftTerms ts))) = _
  rw [liftSubst,liftSubst]

theorem coprimeSubst {α β : Type} (a b : OTerm α) (ts : α → OTerm β) :
    (coprime a b).subst (fun x => emb (ts x)) = coprime (a.subst ts) (b.subst ts) := by
  unfold coprime
  rw [actualUniversalSubstitution,liftEmbedding]
  simp only [onEquality]
  change allOne (((arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc (.var (.inr 0))) (a.relabel Sum.inl)) ⊓ arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc (.var (.inr 0))) (b.relabel Sum.inl))).imp (eqn (suc (.var (.inr 0))) (suc z)) |>.subst (fun x => emb (liftTerms ts x))) = _
  simp only [impSubst,infSubst,dividesSubst,eqnSubst,sucSubst,zSubst,liftSubst]
  rfl

theorem coprimeInstantiate {α : Type} (a b : OTerm (α ⊕ Fin 1)) (s : OTerm α) :
    instantiate (coprime a b) (emb s) = coprime (a.subst (bindTerm s)) (b.subst (bindTerm s)) := by
  rw [instantiate,bindEmbedding,coprimeSubst]

theorem boundedSubst {α β : Type} (p : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (ts : α → OTerm β) :
    (bounded p n).subst (fun x => emb (ts x)) =
      bounded (p.subst (fun x => emb (liftTerms ts x))) (n.subst ts) := by
  unfold bounded
  rw [actualUniversalSubstitution,liftEmbedding,impSubst,orderSubst,liftSubst]
  rfl

theorem boundedRename {α β : Type} (p : Formula (α ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (bounded p n).relabel j = bounded (p.relabel (Sum.map j id)) (n.relabel j) := by
  unfold bounded
  rw [actualUniversalRenaming]
  change allOne ((ltF (.var (.inr 0)) (n.relabel Sum.inl)).relabel (Sum.map j id) |>.imp
    (p.relabel (Sum.map j id))) = _
  simp only [orderRename,Term.relabel_relabel,mapInl,varMap]

theorem boundedElimSyntax {α : Type} (p : Formula (α ⊕ Fin 1)) (s n : OTerm α) :
    instantiate ((ltF (.var (.inr 0)) (n.relabel Sum.inl)).imp p) (emb s) =
      (ltF s n).imp (instantiate p (emb s)) := by
  rw [impInstantiate,orderInstantiate]
  simp only [varBind,liftBind]

theorem coprimeBelowRename {α β : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (coprimeBelow a t n).relabel j =
      coprimeBelow (a.relabel j) (t.relabel (Sum.map j id)) (n.relabel j) := by
  unfold coprimeBelow
  simp only [boundedRename,coprimeRename,sucRelabel,Term.relabel_relabel,mapInl]

theorem dividesBelowRename {α β : Type} (t : OTerm (α ⊕ Fin 1)) (P n : OTerm α) (j : α → β) :
    (dividesBelow t P n).relabel j =
      dividesBelow (t.relabel (Sum.map j id)) (P.relabel j) (n.relabel j) := by
  unfold dividesBelow
  simp only [boundedRename,dividesRename,sucRelabel,Term.relabel_relabel,mapInl]

theorem commonMultipleRename {α β : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (commonMultiple a t n).relabel j =
      commonMultiple (a.relabel j) (t.relabel (Sum.map j id)) (n.relabel j) := by
  unfold commonMultiple
  rw [existsRename]
  change existsOne ((coprime (a.relabel Sum.inl) (suc (.var (.inr 0)))).relabel (Sum.map j id) ⊓
    (dividesBelow (t.relabel (Sum.map Sum.inl id)) (suc (.var (.inr 0))) (n.relabel Sum.inl)).relabel (Sum.map j id)) = _
  rw [coprimeRename,dividesBelowRename]
  simp only [sucRelabel,Term.relabel_relabel,mapInl,varMap]
  congr 3
  congr 1
  funext x; cases x <;> rfl

theorem coprimeBelowSubst {α β : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (ts : α → OTerm β) :
    (coprimeBelow a t n).subst (fun x => emb (ts x)) =
      coprimeBelow (a.subst ts) (t.subst (liftTerms ts)) (n.subst ts) := by
  unfold coprimeBelow
  rw [boundedSubst,coprimeSubst,sucSubst,liftSubst]

theorem dividesBelowSubst {α β : Type} (t : OTerm (α ⊕ Fin 1)) (P n : OTerm α) (ts : α → OTerm β) :
    (dividesBelow t P n).subst (fun x => emb (ts x)) =
      dividesBelow (t.subst (liftTerms ts)) (P.subst ts) (n.subst ts) := by
  unfold dividesBelow
  rw [boundedSubst,dividesSubst,sucSubst,liftSubst]

theorem termLiftBind {α : Type} (t : OTerm (α ⊕ Fin 1)) (s : OTerm α) :
    (t.relabel (Sum.map Sum.inl id)).subst (liftTerms (bindTerm s)) = t := by
  rw [termRelabelSubst]
  have h : liftTerms (bindTerm s) ∘ Sum.map Sum.inl id = Term.var := by
    funext x; cases x <;> rfl
  rw [h,termSubstVar]

theorem commonMatrixInstantiate {α : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n p : OTerm α) :
    instantiate (coprime (a.relabel Sum.inl) (suc (.var (.inr 0))) ⊓
      dividesBelow (t.relabel (Sum.map Sum.inl id)) (suc (.var (.inr 0))) (n.relabel Sum.inl)) (emb p) =
    coprime a (suc p) ⊓ dividesBelow t (suc p) n := by
  rw [infInstantiate]
  rw [coprimeInstantiate,instantiate,bindEmbedding,dividesBelowSubst,termLiftBind]
  simp only [liftBind,sucSubst,varBind]
theorem liftedFamilySubst {α β : Type} (t : OTerm (α ⊕ Fin 1)) (ts : α → OTerm β) :
    (t.relabel (Sum.map Sum.inl id)).subst (liftTerms (liftTerms ts)) =
      (t.subst (liftTerms ts)).relabel (Sum.map Sum.inl id) := by
  rw [termRelabelSubst,termSubstRelabel]
  congr 1
  funext x
  cases x with
  | inl x =>
    simp only [Function.comp_apply,liftTerms,Sum.map_inl,Sum.elim_inl,Term.relabel_relabel]
    rfl
  | inr x => rfl

theorem commonMultipleSubst {α β : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (ts : α → OTerm β) :
    (commonMultiple a t n).subst (fun x => emb (ts x)) =
      commonMultiple (a.subst ts) (t.subst (liftTerms ts)) (n.subst ts) := by
  unfold commonMultiple
  rw [existsSubst,liftEmbedding]
  simp only [infSubst,coprimeSubst,dividesBelowSubst,liftSubst,liftedFamilySubst,sucSubst]
  rfl

theorem commonMultipleInstantiate {α : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) :
    instantiate (commonMultiple (a.relabel Sum.inl) (t.relabel (Sum.map Sum.inl id)) (.var (.inr 0))) (emb n) =
      commonMultiple a t n := by
  rw [instantiate,bindEmbedding,commonMultipleSubst,termLiftBind,liftBind,varBind]

theorem coprimeBelowInstantiate {α : Type} (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) :
    instantiate (coprimeBelow (a.relabel Sum.inl) (t.relabel (Sum.map Sum.inl id)) (.var (.inr 0))) (emb n) =
      coprimeBelow a t n := by
  rw [instantiate,bindEmbedding,coprimeBelowSubst,termLiftBind,liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSyntaxProof
