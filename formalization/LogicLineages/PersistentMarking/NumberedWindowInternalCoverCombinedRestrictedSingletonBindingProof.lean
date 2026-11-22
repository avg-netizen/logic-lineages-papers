module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof
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
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCodeTerm edgeCodeTerm)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs loopArgsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (positiveSubst)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
attribute [local irreducible] programGraph

theorem thinRawRename {α β : Type} (raw : Program 5) (ctx ty q w r : OTerm α) (j : α → β) :
    (thinRawAt raw ctx ty q w r).relabel j = thinRawAt raw (ctx.relabel j) (ty.relabel j)
      (q.relabel j) (w.relabel j) (r.relabel j) := by
  change (programGraph raw (suc z) (loopArgs ctx ty q w r)).relabel j = _
  rw [programRename,loopArgsRename,sucRelabel,zRelabel]
  rfl

variable {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

private theorem leastSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastGraph,programSubst,sucSubst,tape]

theorem thinProvidedRename {β : Type} (ctx cod src wr dst : OTerm α) (j : α → β) :
    (thinProvided C X W s raw ctx cod src wr dst).relabel j = thinProvided C X W s raw
      (ctx.relabel j) (cod.relabel j) (src.relabel j) (wr.relabel j) (dst.relabel j) := by
  simp only [thinProvided,blockRename,thinHopRow,thinHopData,conjunctionRename,leastRename,positiveRename,
    singletonCertificate,hopCodeTerm,edgeCodeTerm,rawConsRename,sucRelabel,zRelabel,Term.relabel_relabel,
    Term.relabel] <;> rfl

private theorem witnessLift (t : OTerm α) (xs : Fin 2 → OTerm α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var xs) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

theorem introduceThinProvided {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (ctx cod src wr dst left right : OTerm α)
    (data : Nonempty (Derivation body Γ (thinHopData C X W s raw ctx cod src wr dst left right))) :
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst)) := by
  let xs : Fin 2 → OTerm α := ![left,right]
  apply actualFiniteExistentialIntroduction body α 2 Γ (thinHopRow C X W s raw ctx cod src wr dst)
    (fun i => emb (xs i))
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext k
    cases k <;> rfl
  rw [h]
  simp only [thinHopRow,thinHopData,conjunctionSubst,leastSubst,positiveSubst,singletonCertificate,hopCodeTerm,
    edgeCodeTerm,rawConsSubst,sucSubst,zSubst,witnessLift,Term.subst,Sum.elim_inr]
  exact data

#print axioms thinRawRename
#print axioms thinProvidedRename
#print axioms introduceThinProvided

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof
