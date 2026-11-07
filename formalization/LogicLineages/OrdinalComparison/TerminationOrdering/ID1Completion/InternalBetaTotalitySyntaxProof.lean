module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalitySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalBinderTransportSyntaxProof
open InternalTermSubstitutionSyntaxProof InternalSourceInversionSupportProof
open InternalGraphCompositionSyntaxProof

/-- Arbitrary term substitution preserves the original two-witness beta body. -/
theorem originalBetaBodySubst {α β : Type} (a b i r : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.betaBody a b i r).subst ts =
      OrdinaryArithmetic.betaBody (a.subst ts) (b.subst ts) (i.subst ts) (r.subst ts) := by
  have ht (t : OrdinaryArithmetic.Term α) :
      (t.relabel (Sum.inl : α → α ⊕ Fin 2)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr)) =
      (t.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]
    rfl
  have hc (p q : OrdinaryArithmetic.arithmeticLanguage.BoundedFormula α 2) :
      (p ⊓ q).subst ts = p.subst ts ⊓ q.subst ts := rfl
  unfold OrdinaryArithmetic.betaBody
  rw [hc]
  simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,Term.bdEqual,
    OrdinaryArithmetic.addTerm,OrdinaryArithmetic.mulTerm,OrdinaryArithmetic.succTerm,
    applyTwoSubstitution,applyOneSubstitution,ht,Term.subst,Sum.elim_inr,Function.comp_apply]

/-- This is substitution in the unchanged original beta formula, over arbitrary names. -/
theorem originalBetaSubst {α β : Type} (a b i r : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (OrdinaryArithmetic.betaFormula a b i r).subst ts =
      OrdinaryArithmetic.betaFormula (a.subst ts) (b.subst ts) (i.subst ts) (r.subst ts) := by
  unfold OrdinaryArithmetic.betaFormula
  rw [exsSubst,originalBetaBodySubst]

/-- Embedding does not change the original beta substitution law. -/
theorem betaSubst {α β : Type} (a b i r : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)).subst
        (fun x => emb (ts x)) =
      arithmeticEmbedding.onFormula
        (OrdinaryArithmetic.betaFormula (a.subst ts) (b.subst ts) (i.subst ts) (r.subst ts)) := by
  rw [← embedSubst,originalBetaSubst]

theorem betaInstantiate {α : Type} (a b i r : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (t : OrdinaryArithmetic.Term α) :
    instantiate (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)) (emb t) =
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula
        (a.subst (bindTerm t)) (b.subst (bindTerm t))
        (i.subst (bindTerm t)) (r.subst (bindTerm t))) := by
  rw [instantiate,bindEmbedding,betaSubst]

theorem betaSuccessor {α : Type} (a b i r : OrdinaryArithmetic.Term (α ⊕ Fin 1)) :
    successorInstance (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)) =
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula
        (a.subst nextTerm) (b.subst nextTerm) (i.subst nextTerm) (r.subst nextTerm)) := by
  rw [successorInstance,nextEmbedding,betaSubst]
open InternalBetaTotality SourceComputabilityFormulaSupportProof
open InternalFiniteBlocksSubstitutionProof InternalDerivationRenamingSyntaxProof
open InternalBetaDivisionSyntaxProof

theorem remainderExistsSubst {α β : Type} (a b i : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (remainderExists a b i).subst (fun x => emb (ts x)) =
      remainderExists (a.subst ts) (b.subst ts) (i.subst ts) := by
  unfold remainderExists
  rw [existsSubst]
  let lift : α ⊕ Fin 1 → OrdinaryArithmetic.Term (β ⊕ Fin 1) :=
    Sum.elim (fun x => (ts x).relabel Sum.inl) (fun j => .var (.inr j))
  have he : Sum.elim (fun x => (emb (ts x)).relabel Sum.inl)
      (fun j : Fin 1 => (Term.var (.inr j) : InternalCalculus.Term (β ⊕ Fin 1))) =
      fun x => emb (lift x) := by
    funext x
    cases x with
    | inl x => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts x)).symm
    | inr j => rfl
  have ht (t : OrdinaryArithmetic.Term α) :
      (t.relabel Sum.inl).subst lift = (t.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]
    rfl
  rw [he,betaSubst]
  simp only [ht]
  rfl

theorem remainderExistsInstantiate {α : Type}
    (a b i : OrdinaryArithmetic.Term (α ⊕ Fin 1)) (t : OrdinaryArithmetic.Term α) :
    instantiate (remainderExists a b i) (emb t) =
      remainderExists (a.subst (bindTerm t)) (b.subst (bindTerm t)) (i.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,remainderExistsSubst]

theorem remainderExistsSuccessor {α : Type} (a b i : OrdinaryArithmetic.Term (α ⊕ Fin 1)) :
    successorInstance (remainderExists a b i) =
      remainderExists (a.subst nextTerm) (b.subst nextTerm) (i.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,remainderExistsSubst]

theorem remainderExistsRename {α β : Type} (a b i : OrdinaryArithmetic.Term α) (j : α → β) :
    (remainderExists a b i).relabel j =
      remainderExists (a.relabel j) (b.relabel j) (i.relabel j) := by
  unfold remainderExists
  simp only [existsRename,betaRename,Term.relabel,Term.relabel_relabel]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalitySyntaxProof
