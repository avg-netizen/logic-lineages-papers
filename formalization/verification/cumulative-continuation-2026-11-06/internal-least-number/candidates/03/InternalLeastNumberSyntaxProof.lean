module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- Disjunction is the existing classical first-order connective. -/
theorem supInstantiate {α : Type} (p q : Formula (α ⊕ Fin 1)) (t : Term α) :
    instantiate (p ⊔ q) t = instantiate p t ⊔ instantiate q t := rfl

open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalPositiveUnfoldingSupportProof InternalDerivationRenamingSyntaxProof
open InternalSourceInversionSupportProof InternalAdditionLawsProof InternalSourceIntroductionSyntaxProof

def liftP {α : Type} (p : Formula (α ⊕ Fin 1)) : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  p.relabel (Sum.map Sum.inl id)
def below {α : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α) : Formula α :=
  allOne ((ltF (.var (.inr 0)) (t.relabel Sum.inl)).imp p.not)
def minP {α : Type} (p : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  p ⊓ below (liftP p) (.var (.inr 0))
def liftTerms {α β : Type} (ts : α → OTerm β) : α ⊕ Fin 1 → OTerm (β ⊕ Fin 1) :=
  Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))

theorem belowSubst {α β : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α)
    (ts : α → OTerm β) :
    (below p t).subst (fun a => emb (ts a)) =
      below (p.subst (fun a => emb (liftTerms ts a))) (t.subst ts) := by
  unfold below
  rw [actualUniversalSubstitution]
  have he : Sum.elim (fun a => (emb (ts a)).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i)) =
      (fun a => emb (liftTerms ts a)) := by
    funext a
    cases a with
    | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
    | inr i => rfl
  rw [he,impSubst,orderSubst,notSubst]
  congr 3
  · rfl
  · rw [termRelabelSubst,termSubstRelabel]
    rfl

theorem belowRename {α β : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α) (j : α → β) :
    (below p t).relabel j = below (p.relabel (Sum.map j id)) (t.relabel j) := by
  unfold below
  rw [actualUniversalRenaming]
  have hr (q r : Formula (α ⊕ Fin 1)) :
      (q.imp r).relabel (Sum.map j id) = (q.relabel (Sum.map j id)).imp (r.relabel (Sum.map j id)) := rfl
  rw [hr,orderRename]
  change allOne ((ltF _ _).imp (p.relabel (Sum.map j id)).not) = _
  congr 3
  · rfl
  · rw [Term.relabel_relabel,Term.relabel_relabel]
    rfl

theorem liftPBind {α : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    (liftP p).subst (fun a => emb (liftTerms (bindTerm t) a)) = p := by
  rw [liftP,actualRelabelSubstitution]
  have he : (fun a => emb (liftTerms (bindTerm t) a)) ∘ Sum.map Sum.inl id = Term.var := by
    funext a
    cases a <;> rfl
  rw [he,formulaSubstVar]

theorem belowInstantiate {α : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (below (liftP p) (.var (.inr 0))) (emb t) = below p t := by
  rw [instantiate,bindEmbedding,belowSubst,liftPBind]
  rfl

theorem liftPNext {α : Type} (p : Formula (α ⊕ Fin 1)) :
    (liftP p).subst (fun a => emb (liftTerms nextTerm a)) = liftP p := by
  rw [liftP,actualRelabelSubstitution,formulaRelabelAsSubst]
  rfl

theorem belowSuccessor {α : Type} (p : Formula (α ⊕ Fin 1)) :
    successorInstance (below (liftP p) (.var (.inr 0))) =
      below (liftP p) (suc (.var (.inr 0))) := by
  rw [successorInstance,nextEmbedding,belowSubst,liftPNext]
  rfl

theorem belowElimSyntax {α : Type} (p : Formula (α ⊕ Fin 1)) (s t : OTerm α) :
    instantiate ((ltF (.var (.inr 0)) (t.relabel Sum.inl)).imp p.not) (emb s) =
      (ltF s t).imp (instantiate p (emb s)).not := by
  rw [impInstantiate,orderInstantiate,notInstantiate]
  simp only [varBind,liftBind]

theorem minRename {α β : Type} (p : Formula (α ⊕ Fin 1)) (j : α → β) :
    (minP p).relabel (Sum.map j id) = minP (p.relabel (Sum.map j id)) := by
  change p.relabel (Sum.map j id) ⊓ (below (liftP p) (.var (.inr 0))).relabel (Sum.map j id) = _
  rw [belowRename]
  unfold minP liftP
  rw [formulaRelabelComposition,formulaRelabelComposition]
  congr 3
  funext a
  cases a <;> rfl

theorem minInstantiate {α : Type} (p : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (minP p) (emb t) = instantiate p (emb t) ⊓ below p t := by
  change instantiate p (emb t) ⊓ instantiate (below (liftP p) (.var (.inr 0))) (emb t) = _
  rw [belowInstantiate]

theorem freshP {α : Type} (p : Formula (α ⊕ Fin 1)) :
    instantiate (liftP p) (emb (.var (.inr 0))) = p :=
  actualFreshInstantiation α p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
