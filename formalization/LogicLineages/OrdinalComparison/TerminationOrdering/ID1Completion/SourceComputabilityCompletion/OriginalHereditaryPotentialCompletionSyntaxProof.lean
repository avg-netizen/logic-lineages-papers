module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalAdditionLawsProof (impSubst)
open InternalComputabilityApplicationSyntaxProof (programSubst)
open OriginalHereditaryInternalAgendaSyntaxProof (agendaSubst agendaRename)
open OriginalHereditaryPotentialCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type}
theorem entrySubst {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel input work results before output : OTerm alpha) (ts : alpha → OTerm beta) :
 (Entry R H M W c B fuel input work results before output).subst (fun a => emb (ts a)) =
 Entry R H M W (c.subst ts) (B.subst ts) (fuel.subst ts) (input.subst ts) (work.subst ts) (results.subst ts) (before.subst ts) (output.subst ts) := by
 simp only [Entry,conjunctionSubst,agendaSubst,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,InternalRawListRecursionSyntaxProof.emptySubst,orderSubst,sucSubst]
theorem emptySubst {beta : Type} (output : OTerm alpha) (ts : alpha → OTerm beta) :
 (OriginalHereditaryPotentialCompletion.Empty output).subst (fun a => emb (ts a)) = OriginalHereditaryPotentialCompletion.Empty (output.subst ts) := by
 simp only [OriginalHereditaryPotentialCompletion.Empty,graph1,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,InternalRawListRecursionSyntaxProof.emptySubst,zSubst]
theorem entryRename {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel input work results before output : OTerm alpha) (j : alpha → beta) :
 (Entry R H M W c B fuel input work results before output).relabel j =
 Entry R H M W (c.relabel j) (B.relabel j) (fuel.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (before.relabel j) (output.relabel j) := by
 simp only [Entry,conjunctionRename,agendaRename,graph2Rename,orderRename,sucRelabel]
theorem emptyRename {beta : Type} (output : OTerm alpha) (j : alpha → beta) :
 (OriginalHereditaryPotentialCompletion.Empty output).relabel j = OriginalHereditaryPotentialCompletion.Empty (output.relabel j) := by simp only [OriginalHereditaryPotentialCompletion.Empty,graph1Rename,zRelabel]
theorem rowSubst {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel : OTerm alpha) (ts : alpha → OTerm beta) :
 (Row R H M W c B fuel).subst (fun a => emb (ts a)) = Row R H M W (c.subst ts) (B.subst ts) (fuel.subst ts) := by
 unfold Row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [entrySubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel : OTerm alpha) (j : alpha → beta) :
 (Row R H M W c B fuel).relabel j = Row R H M W (c.relabel j) (B.relabel j) (fuel.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Row R H M W c B fuel).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel input work results before output : OTerm alpha) :
 (rowBody R H M W c B fuel).subst (Sum.elim Term.var (fun i => emb (![input,work,results,before,output] i))) =
 (Entry R H M W c B fuel input work results before output).imp (OriginalHereditaryPotentialCompletion.Empty output) := by
 have he : (Sum.elim Term.var (fun i => emb (![input,work,results,before,output] i))) =
  (fun a => emb (Sum.elim Term.var ![input,work,results,before,output] a)) := by funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [entrySubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (Row R H M W c B fuel) (emb t) = Row R H M W (c.subst (bindTerm t)) (B.subst (bindTerm t)) (fuel.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (Row R H M W c B fuel) = Row R H M W (c.subst nextTerm) (B.subst nextTerm) (fuel.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
