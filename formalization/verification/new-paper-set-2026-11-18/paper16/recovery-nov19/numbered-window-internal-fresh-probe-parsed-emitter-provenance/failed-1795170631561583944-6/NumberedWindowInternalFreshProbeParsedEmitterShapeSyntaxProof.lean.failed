module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterShapeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename equalEqn)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction)
open ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof (blockRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqnRelabel eqnSubst zRelabel sucRelabel zSubst sucSubst)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename unarySubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

private def factors {α : Type} (bound : Program 1) (q u c r d e k n : OTerm α) : Formula α :=
  addressReports q c r k ⊓ (arrowReports q d e ⊓ (sourceShape q c r d e k ⊓
    (programGraph bound n ![k] ⊓ equal u (packedFreeTerm c d n))))

private def matrix {α : Type} (bound : Program 1) (q u : OTerm α) : Formula (α ⊕ Fin 6) :=
  factors bound (q.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))

private theorem shapeMatrix {α : Type} (bound : Program 1) (q u : OTerm α) :
    parsedFreshAt bound q u = block (matrix bound q u) := rfl

private theorem factorsRename {α β : Type} (bound : Program 1) (q u c r d e k n : OTerm α)
    (j : α → β) :
    (factors bound q u c r d e k n).relabel j = factors bound (q.relabel j) (u.relabel j)
      (c.relabel j) (r.relabel j) (d.relabel j) (e.relabel j) (k.relabel j) (n.relabel j) := by
  simp only [factors,addressReports,arrowReports,sourceShape,equalEqn,
    conjunctionRename,programRename,unaryRename,eqnRelabel,
    addressTerm,packedFreeTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem factorsSubst {α β : Type} (bound : Program 1) (q u c r d e k n : OTerm α)
    (s : α → OTerm β) :
    (factors bound q u c r d e k n).subst (fun x => emb (s x)) = factors bound (q.subst s) (u.subst s)
      (c.subst s) (r.subst s) (d.subst s) (e.subst s) (k.subst s) (n.subst s) := by
  simp only [factors,addressReports,arrowReports,sourceShape,equalEqn,
    conjunctionSubst,programSubst,unarySubst,eqnSubst,
    addressTerm,packedFreeTerm,consTerm,pairTerm,addSubst,mulSubst,sucSubst,zSubst,numeralSubst]

theorem parsedRename {α β : Type} (bound : Program 1) (q u : OTerm α) (j : α → β) :
    (parsedFreshAt bound q u).relabel j = parsedFreshAt bound (q.relabel j) (u.relabel j) := by
  simp only [shapeMatrix,blockRename,matrix,factorsRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem matrixInstantiate {α : Type} (bound : Program 1) (q u : OTerm α)
    (ys : Fin 6 → OTerm α) :
    (matrix bound q u).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      factors bound q u (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) := by
  let sub : α ⊕ Fin 6 → OTerm α := Sum.elim Term.var ys
  have hsub : Sum.elim Term.var (fun i => emb (ys i)) = (fun x => emb (sub x)) := by
    funext x
    cases x <;> rfl
  have hfree (a : OTerm α) : (a.relabel Sum.inl).subst sub = a := by
    rw [termRelabelSubst]
    exact termSubstVar a
  have hbound (i : Fin 6) : (Term.var (.inr i) : OTerm (α ⊕ Fin 6)).subst sub = ys i := rfl
  simp only [hsub,matrix,factorsSubst,hfree,hbound]

/-- Each of the six actual reports is introduced at its literal index;
q and u remain the original free terms throughout the block. -/
theorem parsedIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (bound : Program 1) (q u : OTerm α) (ys : Fin 6 → OTerm α)
    (ha : Nonempty (Derivation body Γ (addressReports q (ys 0) (ys 1) (ys 4))))
    (hb : Nonempty (Derivation body Γ (arrowReports q (ys 2) (ys 3))))
    (hs : Nonempty (Derivation body Γ (sourceShape q (ys 0) (ys 1) (ys 2) (ys 3) (ys 4))))
    (hn : Nonempty (Derivation body Γ (programGraph bound (ys 5) ![ys 4])))
    (he : Nonempty (Derivation body Γ (equal u (packedFreeTerm (ys 0) (ys 2) (ys 5))))) :
    Nonempty (Derivation body Γ (parsedFreshAt bound q u)) := by
  rw [shapeMatrix]
  apply actualFiniteExistentialIntroduction body α 6 Γ (matrix bound q u) (fun i => emb (ys i))
  rw [matrixInstantiate]
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  obtain ⟨ds⟩ := hs
  obtain ⟨dn⟩ := hn
  obtain ⟨de⟩ := he
  exact ⟨Derivation.conjunctionIntroduction da (Derivation.conjunctionIntroduction db
    (Derivation.conjunctionIntroduction ds (Derivation.conjunctionIntroduction dn de)))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterShapeSyntaxProof
