module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding allBlockSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalGraphCompositionSyntaxProof (bindSubst exsSubst)
open ID1Completion.InternalTermSubstitutionProof (actualUniversalSubstitution)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind zSubst sucSubst nextEmbedding)
open ID1Completion.InternalAdditionLawsProof (impSubst liftNext varNext)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedSuccessorTargets (termProjection argsProjection)
open NumberedWindowInternalCoverSelectedGrammarTargets
open NumberedWindowInternalCoverSelectedGrammarWidthTargets
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] programGraph
variable {α β : Type}

private theorem quadTapeSubst (d H K M : OTerm α) (ts : α → OTerm β) :
    (fun i => (grammarTape d H K M i).subst ts) =
      grammarTape (d.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i

private theorem unaryTapeSubst (x : OTerm α) (ts : α → OTerm β) :
    (fun i : Fin 1 => ((![x] : Fin 1 → OTerm α) i).subst ts) = ![x.subst ts] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

private theorem unarySubst (P : Program 1) (out x : OTerm α) (ts : α → OTerm β) :
    (unary P out x).subst (fun a => emb (ts a)) =
      unary P (out.subst ts) (x.subst ts) := by
  unfold unary
  rw [programSubst,unaryTapeSubst]

theorem observedSubst (d H K M state terms args : OTerm α) (ts : α → OTerm β) :
    (observed d H K M state terms args).subst (fun a => emb (ts a)) =
      observed (d.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) (state.subst ts)
        (terms.subst ts) (args.subst ts) := by
  simp only [observed,conjunctionSubst,grammarReport,programSubst,quadTapeSubst,
    termProjection,argsProjection,unarySubst]

theorem observedRename (d H K M state terms args : OTerm α) (j : α → β) :
    (observed d H K M state terms args).relabel j =
      observed (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) (state.relabel j)
        (terms.relabel j) (args.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observed d H K M state terms args).subst (fun a => emb (.var (j a))) = _
  rw [observedSubst]
  simp only [← termRelabelAsSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (ts : α → Term β) :
    (block phi).subst ts = block (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem observationSubst (d H K M : OTerm α) (ts : α → OTerm β) :
    (existingObservation d H K M).subst (fun a => emb (ts a)) =
      existingObservation (d.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  unfold existingObservation observationMatrix
  rw [blockSubst,liftedEmbedding,observedSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem observationRename (d H K M : OTerm α) (j : α → β) :
    (existingObservation d H K M).relabel j =
      existingObservation (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (existingObservation d H K M).subst (fun a => emb (.var (j a))) = _
  rw [observationSubst]
  simp only [← termRelabelAsSubst]

private theorem axisSubst (xs ys : OTerm α) (ts : α → OTerm β) :
    (axisInclusion xs ys).subst (fun a => emb (ts a)) =
      axisInclusion (xs.subst ts) (ys.subst ts) := by
  unfold axisInclusion
  rw [actualUniversalSubstitution,liftedEmbedding,impSubst,memberSubst,memberSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem comparedSubst (d H K m M : OTerm α) (w : Fin 6 → OTerm α) (ts : α → OTerm β) :
    (compared d H K m M w).subst (fun a => emb (ts a)) =
      compared (d.subst ts) (H.subst ts) (K.subst ts) (m.subst ts) (M.subst ts)
        (fun i => (w i).subst ts) := by
  unfold compared
  rw [impSubst,conjunctionSubst]
  rw [observedSubst d H K m (w 0) (w 1) (w 2) ts,
    observedSubst d H K M (w 3) (w 4) (w 5) ts]
  simp only [pairInclusion,conjunctionSubst,axisSubst]

private theorem widthSubst (d H K m M : OTerm α) (ts : α → OTerm β) :
    (widthAt d H K m M).subst (fun a => emb (ts a)) =
      widthAt (d.subst ts) (H.subst ts) (K.subst ts) (m.subst ts) (M.subst ts) := by
  unfold widthAt widthMatrix
  rw [allBlockSubst,liftedEmbedding,comparedSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem widthRename (d H K m M : OTerm α) (j : α → β) :
    (widthAt d H K m M).relabel j =
      widthAt (d.relabel j) (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (widthAt d H K m M).subst (fun a => emb (.var (j a))) = _
  rw [widthSubst]
  simp only [← termRelabelAsSubst]

theorem widthInstance (d H K m M : OTerm α) :
    instantiate (widthMotive H K m M) (emb d) = widthAt d H K m M := by
  simp only [instantiate,bindEmbedding,widthMotive,widthSubst,liftBind,varBind]

theorem widthNext (H K m M : OTerm α) :
    successorInstance (widthMotive H K m M) =
      widthAt (ID1Completion.InternalTagArithmeticSyntaxProof.suc (.var (.inr 0)))
        (H.relabel Sum.inl) (K.relabel Sum.inl) (m.relabel Sum.inl) (M.relabel Sum.inl) := by
  simp only [successorInstance,nextEmbedding,widthMotive,widthSubst,liftNext,varNext]

theorem widthWitness (d H K m M : OTerm α) (w : Fin 6 → OTerm α) :
    (widthMatrix d H K m M).subst (Sum.elim Term.var (fun i => emb (w i))) = compared d H K m M w := by
  have he : Sum.elim Term.var (fun i => emb (w i)) = (fun x => emb (Sum.elim Term.var w x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold widthMatrix
  rw [comparedSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem observationWitness (d H K M : OTerm α) (w : Fin 3 → OTerm α) :
    (observationMatrix d H K M).subst (Sum.elim Term.var (fun i => emb (w i))) =
      observed d H K M (w 0) (w 1) (w 2) := by
  have he : Sum.elim Term.var (fun i => emb (w i)) = (fun x => emb (Sum.elim Term.var w x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold observationMatrix
  rw [observedSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
