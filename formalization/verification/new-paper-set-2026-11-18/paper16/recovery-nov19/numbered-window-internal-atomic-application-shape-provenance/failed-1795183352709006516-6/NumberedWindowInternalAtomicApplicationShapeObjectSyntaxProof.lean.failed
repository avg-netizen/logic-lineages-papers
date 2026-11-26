module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction)
open ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof (blockRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (numeralSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqnRelabel eqnSubst zRelabel sucRelabel zSubst sucSubst)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets

private def factors {α : Type} (c t k u y d e a a' : OTerm α) : Formula α :=
  equal t (consTerm d e) ⊓ (equal u (addressTerm c d a) ⊓ equal y (auxAddressTerm c d e k a'))

private def matrix {α : Type} (c t k u y : OTerm α) : Formula (α ⊕ Fin 4) :=
  factors (c.relabel Sum.inl) (t.relabel Sum.inl) (k.relabel Sum.inl)
    (u.relabel Sum.inl) (y.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

private theorem shapeMatrix {α : Type} (c t k u y : OTerm α) :
    literalApplicationShape c t k u y = block (matrix c t k u y) := rfl

private theorem factorsRename {α β : Type} (c t k u y d e a a' : OTerm α) (j : α → β) :
    (factors c t k u y d e a a').relabel j = factors (c.relabel j) (t.relabel j) (k.relabel j)
      (u.relabel j) (y.relabel j) (d.relabel j) (e.relabel j) (a.relabel j) (a'.relabel j) := by
  simp only [factors,equalEqn,eqnRelabel,conjunctionRename,auxAddressTerm,addressTerm,consTerm,pairTerm,
    addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem factorsSubst {α β : Type} (c t k u y d e a a' : OTerm α) (s : α → OTerm β) :
    (factors c t k u y d e a a').subst (fun x => emb (s x)) = factors (c.subst s) (t.subst s) (k.subst s)
      (u.subst s) (y.subst s) (d.subst s) (e.subst s) (a.subst s) (a'.subst s) := by
  simp only [factors,equalEqn,eqnSubst,conjunctionSubst,auxAddressTerm,addressTerm,consTerm,pairTerm,
    addSubst,mulSubst,sucSubst,zSubst,numeralSubst]

theorem shapeRename {α β : Type} (c t k u y : OTerm α) (j : α → β) :
    (literalApplicationShape c t k u y).relabel j =
      literalApplicationShape (c.relabel j) (t.relabel j) (k.relabel j) (u.relabel j) (y.relabel j) := by
  simp only [shapeMatrix,blockRename,matrix,factorsRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem matrixInstantiate {α : Type} (c t k u y : OTerm α) (ys : Fin 4 → OTerm α) :
    (matrix c t k u y).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      factors c t k u y (ys 0) (ys 1) (ys 2) (ys 3) := by
  let s : α ⊕ Fin 4 → OTerm α := Sum.elim Term.var ys
  have hsub : Sum.elim Term.var (fun i => emb (ys i)) = (fun x => emb (s x)) := by
    funext x
    cases x <;> rfl
  have hfree (x : OTerm α) : (x.relabel Sum.inl).subst s = x := by
    rw [termRelabelSubst]
    exact termSubstVar x
  have hbound (i : Fin 4) : (Term.var (.inr i) : OTerm (α ⊕ Fin 4)).subst s = ys i := rfl
  simp only [hsub,matrix,factorsSubst,hfree,hbound]

theorem shapeIntro {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (c t k u y : OTerm α) (ys : Fin 4 → OTerm α)
    (arrow : Nonempty (Derivation B Γ (equal t (consTerm (ys 0) (ys 1)))))
    (arg : Nonempty (Derivation B Γ (equal u (addressTerm c (ys 0) (ys 2)))))
    (out : Nonempty (Derivation B Γ (equal y (auxAddressTerm c (ys 0) (ys 1) k (ys 3))))) :
    Nonempty (Derivation B Γ (literalApplicationShape c t k u y)) := by
  rw [shapeMatrix]
  apply actualFiniteExistentialIntroduction B α 4 Γ (matrix c t k u y) (fun i => emb (ys i))
  rw [matrixInstantiate]
  obtain ⟨a⟩ := arrow
  obtain ⟨b⟩ := arg
  obtain ⟨d⟩ := out
  exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b d)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
