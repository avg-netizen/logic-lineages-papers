module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedRename suppliedSubst)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
attribute [local irreducible] programGraph

variable {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

private theorem leastSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastGraph,programSubst,sucSubst,tape]

theorem suppliedPathRename {β : Type} (ctx cod src dst : OTerm α) (j : α → β) :
    (suppliedPath C X W s raw ctx cod src dst).relabel j = suppliedPath C X W s raw
      (ctx.relabel j) (cod.relabel j) (src.relabel j) (dst.relabel j) := by
  simp only [suppliedPath,blockRename,pathRow,pathData,conjunctionRename,leastRename,suppliedRename,
    Term.relabel_relabel,Term.relabel] <;> rfl

private theorem witnessLift (t : OTerm α) (xs : Fin 2 → OTerm α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var xs) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

theorem introduceSuppliedPath {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (ctx cod src dst left right : OTerm α)
    (data : Nonempty (Derivation body Γ (pathData C X W s raw ctx cod src dst left right))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  let xs : Fin 2 → OTerm α := ![left,right]
  apply actualFiniteExistentialIntroduction body α 2 Γ (pathRow C X W s raw ctx cod src dst)
    (fun i => emb (xs i))
  have h : (Sum.elim Term.var (fun i => emb (xs i))) =
      (fun a => emb (Sum.elim Term.var xs a)) := by
    funext k
    cases k <;> rfl
  rw [h]
  simp only [pathRow,pathData,conjunctionSubst,leastSubst,suppliedSubst,witnessLift,Term.subst,Sum.elim_inr]
  exact data

#print axioms suppliedPathRename
#print axioms introduceSuppliedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof
