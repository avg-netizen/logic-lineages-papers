module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseApplicationHopTargets
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCodeTerm edgeCodeTerm)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs loopArgsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (positiveSubst)
open NumberedWindowInternalSparseRoundLeastSyntaxProof (leastSubst)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
attribute [local irreducible] programGraph

theorem rawRename {α β : Type} (raw : Program 5) (ctx ty q w r : OTerm α) (j : α → β) :
    (rawAt raw ctx ty q w r).relabel j = rawAt raw (ctx.relabel j) (ty.relabel j)
      (q.relabel j) (w.relabel j) (r.relabel j) := by
  change (programGraph raw (suc z) (loopArgs ctx ty q w r)).relabel j = _
  rw [programRename,loopArgsRename,sucRelabel,zRelabel]
  rfl

variable {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem providedRename {β : Type} (ctx cod src wr dst : OTerm α) (j : α → β) :
    (provided C X W s raw ctx cod src wr dst).relabel j = provided C X W s raw
      (ctx.relabel j) (cod.relabel j) (src.relabel j) (wr.relabel j) (dst.relabel j) := by
  simp only [provided,blockRename,row,hopData,conjunctionRename,leastRename,positiveRename,
    singletonCertificate,hopCodeTerm,edgeCodeTerm,rawConsRename,sucRelabel,zRelabel,Term.relabel_relabel,
    Term.relabel] <;> rfl

private theorem witnessLift (t : OTerm α) (xs : Fin 2 → OTerm α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var xs) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

theorem introduce {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (ctx cod src wr dst left right : OTerm α)
    (data : Nonempty (Derivation body Γ (hopData C X W s raw ctx cod src wr dst left right))) :
    Nonempty (Derivation body Γ (provided C X W s raw ctx cod src wr dst)) := by
  let xs : Fin 2 → OTerm α := ![left,right]
  apply actualFiniteExistentialIntroduction body α 2 Γ (row C X W s raw ctx cod src wr dst)
    (fun i => emb (xs i))
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext k
    cases k <;> rfl
  rw [h]
  simp only [row,hopData,conjunctionSubst,leastSubst,positiveSubst,singletonCertificate,hopCodeTerm,
    edgeCodeTerm,rawConsSubst,sucSubst,zSubst,witnessLift,Term.subst,Sum.elim_inr]
  exact data

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopBindingProof
