module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedLiteralSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
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
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets (literalParsedAt)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename unarySubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[expose] def rawFactors {α : Type} (bound : Program 1) (q u c r d e k n : OTerm α) : Formula α :=
  addressReports q c r k ⊓ (arrowReports q d e ⊓ (sourceShape q c r d e k ⊓
    (programGraph bound n ![k] ⊓ equal u (packedFreeTerm c d n))))

@[expose] def rawMatrix {α : Type} (bound : Program 1) (q u : OTerm α) : Formula (α ⊕ Fin 6) :=
  rawFactors bound (q.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))

theorem rawBlock {α : Type} (bound : Program 1) (q u : OTerm α) :
    parsedFreshAt bound q u = block (rawMatrix bound q u) := rfl

private def checkedFactors {α : Type} (bound : Program 1) (σ τ : ProbeTy)
    (q u c r d e k n : OTerm α) : Formula α :=
  addressReports q c r k ⊓ (arrowReports q d e ⊓ (sourceShape q c r d e k ⊓
    (programGraph bound n ![k] ⊓
      (equal u (packedFreeTerm c d n) ⊓ (equal d (numeral (typeCode σ)) ⊓ equal e (numeral (typeCode τ)))))))

private def checkedMatrix {α : Type} (bound : Program 1) (σ τ : ProbeTy) (q u : OTerm α) : Formula (α ⊕ Fin 6) :=
  checkedFactors bound σ τ (q.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))

private theorem literalBlock {α : Type} (bound : Program 1) (σ τ : ProbeTy) (q u : OTerm α) :
    literalParsedAt bound σ τ q u = block (checkedMatrix bound σ τ q u) := rfl

private theorem factorsRename {α β : Type} (bound : Program 1) (σ τ : ProbeTy) (q u c r d e k n : OTerm α)
    (j : α → β) :
    (checkedFactors bound σ τ q u c r d e k n).relabel j =
      checkedFactors bound σ τ (q.relabel j) (u.relabel j) (c.relabel j) (r.relabel j)
        (d.relabel j) (e.relabel j) (k.relabel j) (n.relabel j) := by
  simp only [checkedFactors,addressReports,arrowReports,sourceShape,equalEqn,
    conjunctionRename,programRename,unaryRename,eqnRelabel,
    addressTerm,packedFreeTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem factorsSubst {α β : Type} (bound : Program 1) (σ τ : ProbeTy) (q u c r d e k n : OTerm α)
    (s : α → OTerm β) :
    (checkedFactors bound σ τ q u c r d e k n).subst (fun x => emb (s x)) =
      checkedFactors bound σ τ (q.subst s) (u.subst s) (c.subst s) (r.subst s)
        (d.subst s) (e.subst s) (k.subst s) (n.subst s) := by
  simp only [checkedFactors,addressReports,arrowReports,sourceShape,equalEqn,
    conjunctionSubst,programSubst,unarySubst,eqnSubst,
    addressTerm,packedFreeTerm,consTerm,pairTerm,addSubst,mulSubst,sucSubst,zSubst,numeralSubst]

theorem literalRename {α β : Type} (bound : Program 1) (σ τ : ProbeTy)
    (q u : OTerm α) (j : α → β) :
    (literalParsedAt bound σ τ q u).relabel j = literalParsedAt bound σ τ (q.relabel j) (u.relabel j) := by
  simp only [literalBlock,blockRename,checkedMatrix,factorsRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem matrixInstantiate {α : Type} (bound : Program 1) (σ τ : ProbeTy) (q u : OTerm α)
    (ys : Fin 6 → OTerm α) :
    (checkedMatrix bound σ τ q u).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      checkedFactors bound σ τ q u (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) := by
  let sub : α ⊕ Fin 6 → OTerm α := Sum.elim Term.var ys
  have hsub : Sum.elim Term.var (fun i => emb (ys i)) = (fun x => emb (sub x)) := by
    funext x
    cases x <;> rfl
  have hfree (a : OTerm α) : (a.relabel Sum.inl).subst sub = a := by
    rw [termRelabelSubst]
    exact termSubstVar a
  have hbound (i : Fin 6) : (Term.var (.inr i) : OTerm (α ⊕ Fin 6)).subst sub = ys i := rfl
  simp only [hsub,checkedMatrix,factorsSubst,hfree,hbound]

/-- Preserve the actual same-slot raw matrix and add both independently
derived literal equations. No binder is dropped, duplicated or reordered. -/
theorem literalIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (bound : Program 1) (σ τ : ProbeTy) (q u : OTerm α) (ys : Fin 6 → OTerm α)
    (raw : Nonempty (Derivation body Γ (rawFactors bound q u (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))))
    (literal : Nonempty (Derivation body Γ
      (equal (ys 2) (numeral (typeCode σ)) ⊓ equal (ys 3) (numeral (typeCode τ))))) :
    Nonempty (Derivation body Γ (literalParsedAt bound σ τ q u)) := by
  rw [literalBlock]
  apply actualFiniteExistentialIntroduction body α 6 Γ (checkedMatrix bound σ τ q u) (fun i => emb (ys i))
  rw [matrixInstantiate]
  obtain ⟨a⟩ := raw
  obtain ⟨b⟩ := literal
  have h1 := Derivation.conjunctionRight a
  have h2 := Derivation.conjunctionRight h1
  have h3 := Derivation.conjunctionRight h2
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft a)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h1)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h2)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h3)
          (Derivation.conjunctionIntroduction (Derivation.conjunctionRight h3) b))))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedLiteralSyntaxProof
