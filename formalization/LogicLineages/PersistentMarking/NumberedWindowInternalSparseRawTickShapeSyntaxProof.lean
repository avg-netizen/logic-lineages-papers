module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalBetaBoundaryProof (supRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTerms liftTermSubst existsEmbeddedSubst)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn bindEmbedding bindTerm liftBind varBind eqnSubst eqnRelabel sucSubst zSubst zRelabel)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeTargets

theorem stateRename {α β : Type} (a b : OTerm α) (j : α → β) :
    (stateTerm a b).relabel j = stateTerm (a.relabel j) (b.relabel j) := by
  unfold stateTerm
  rw [rawConsRename,rawConsRename,zRelabel]

theorem rawConsSubst {α β : Type} (x y : OTerm α) (ts : α → OTerm β) :
    (rawCons x y).subst ts = rawCons (x.subst ts) (y.subst ts) := by
  unfold rawCons pairTerm
  simp only [sucSubst,addSubst,mulSubst]

theorem stateSubst {α β : Type} (a b : OTerm α) (ts : α → OTerm β) :
    (stateTerm a b).subst ts = stateTerm (a.subst ts) (b.subst ts) := by
  unfold stateTerm
  rw [rawConsSubst,rawConsSubst,zSubst]

/-- Quantifier-free matrix of `goodState` at explicit witnesses. -/
def shapeCore {α : Type} (o f F : OTerm α) : Formula α :=
  eqn o (stateTerm f F) ⊓ (eqn f z ⊔ eqn F z)

theorem goodUnfold {α : Type} (out : OTerm α) :
    goodState out = existsOne (existsOne (shapeCore
      ((out.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
      (.var (.inl (.inr 0))) (.var (.inr 0)))) := rfl

theorem coreSubst {α β : Type} (o f F : OTerm α) (ts : α → OTerm β) :
    (shapeCore o f F).subst (fun a => emb (ts a)) =
      shapeCore (o.subst ts) (f.subst ts) (F.subst ts) := by
  change (eqn o (stateTerm f F)).subst (fun a => emb (ts a)) ⊓
    ((eqn f z).subst (fun a => emb (ts a)) ⊔ (eqn F z).subst (fun a => emb (ts a))) = _
  rw [eqnSubst,eqnSubst,eqnSubst,stateSubst,zSubst]
  rfl

theorem coreRename {α β : Type} (o f F : OTerm α) (j : α → β) :
    (shapeCore o f F).relabel j = shapeCore (o.relabel j) (f.relabel j) (F.relabel j) := by
  change (eqn o (stateTerm f F)).relabel j ⊓ ((eqn f z).relabel j ⊔ (eqn F z).relabel j) = _
  rw [eqnRelabel,eqnRelabel,eqnRelabel,stateRename,zRelabel]
  rfl

theorem goodRename {α β : Type} (out : OTerm α) (j : α → β) :
    (goodState out).relabel j = goodState (out.relabel j) := by
  rw [goodUnfold,goodUnfold,existsRename,existsRename,coreRename]
  simp only [Term.relabel_relabel]
  rfl

/-- Introduce both literal quantifiers at explicit witnesses (flag first,
then frame) from an actual scratch equation and an actual zero disjunct. -/
theorem goodIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (out a b : OTerm α)
    (he : Nonempty (Derivation body Γ (eqn out (stateTerm a b))))
    (hz : Nonempty (Derivation body Γ (eqn a z ⊔ eqn b z))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  let o' : OTerm (α ⊕ Fin 1) := out.relabel Sum.inl
  let a' : OTerm (α ⊕ Fin 1) := a.relabel Sum.inl
  let A : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    shapeCore (o'.relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))
  let B : Formula (α ⊕ Fin 1) := shapeCore o' a' (.var (.inr 0))
  have firstSlot :
      (Term.var (.inl (.inr 0)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst
        (liftTerms (bindTerm a)) = a' := rfl
  have lastSlot :
      (Term.var (.inr 0) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst (liftTerms (bindTerm a)) =
        (Term.var (.inr 0) : OTerm (α ⊕ Fin 1)) := rfl
  have ho : instantiate (existsOne A) (emb a) = existsOne B := by
    simp only [instantiate,bindEmbedding,existsEmbeddedSubst,A,B,coreSubst,liftTermSubst,
      o',liftBind,firstSlot,lastSlot]
  have hi : instantiate B (emb b) = shapeCore out a b := by
    simp only [instantiate,bindEmbedding,B,o',a',coreSubst,liftBind,varBind]
  obtain ⟨de⟩ := he
  obtain ⟨dz⟩ := hz
  change Nonempty (Derivation body Γ (existsOne (existsOne A)))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb a)
  rw [ho]
  apply Derivation.existentialIntroduction (emb b)
  rw [hi]
  exact Derivation.conjunctionIntroduction de dz

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
