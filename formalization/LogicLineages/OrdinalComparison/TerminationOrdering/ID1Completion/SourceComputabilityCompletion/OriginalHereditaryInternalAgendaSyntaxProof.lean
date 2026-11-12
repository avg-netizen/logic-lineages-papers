module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalHereditaryInternalAgenda
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst numeralSubst)
open InternalFiniteBlocks (block)
theorem jobFieldsSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B job role typ typed rawJob raw parameter gamma weight : OTerm alpha) (ts : alpha → OTerm beta) :
 (jobFields H M W c B job role typ typed rawJob raw parameter gamma weight).subst (fun a => emb (ts a)) =
 jobFields H M W (c.subst ts) (B.subst ts) (job.subst ts) (role.subst ts) (typ.subst ts) (typed.subst ts) (rawJob.subst ts) (raw.subst ts) (parameter.subst ts) (gamma.subst ts) (weight.subst ts) := by
 simp only [jobFields,Below,conjunctionSubst,orderSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,admissibleSubst,sucSubst]
theorem jobSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B job : OTerm alpha) (ts : alpha → OTerm beta) :
 (Job H M W c B job).subst (fun a => emb (ts a)) =
 Job H M W (c.subst ts) (B.subst ts) (job.subst ts) := by
 unfold Job jobMatrix
 rw [blockSubst,liftedEmbedding,jobFieldsSubst]
 simp only [liftSubst,Term.subst,Sum.elim_inr]
theorem jobFieldsRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B job role typ typed rawJob raw parameter gamma weight : OTerm alpha) (j : alpha → beta) :
 (jobFields H M W c B job role typ typed rawJob raw parameter gamma weight).relabel j =
 jobFields H M W (c.relabel j) (B.relabel j) (job.relabel j) (role.relabel j) (typ.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (weight.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (jobFields H M W c B job role typ typed rawJob raw parameter gamma weight).subst (fun a => emb (.var (j a))) = _
 rw [jobFieldsSubst]
 simp only [← termRelabelAsSubst]
theorem jobRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B job : OTerm alpha) (j : alpha → beta) :
 (Job H M W c B job).relabel j =
 Job H M W (c.relabel j) (B.relabel j) (job.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Job H M W c B job).subst (fun a => emb (.var (j a))) = _
 rw [jobSubst]
 simp only [← termRelabelAsSubst]
theorem frameFieldsSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B frame parent payload counts : OTerm alpha) (ts : alpha → OTerm beta) :
 (frameFields H M W c B frame parent payload counts).subst (fun a => emb (ts a)) =
 frameFields H M W (c.subst ts) (B.subst ts) (frame.subst ts) (parent.subst ts) (payload.subst ts) (counts.subst ts) := by
 simp only [frameFields,Below,conjunctionSubst,orderSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,orSubst,numeralSubst,jobSubst]
theorem frameSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B frame : OTerm alpha) (ts : alpha → OTerm beta) :
 (Frame H M W c B frame).subst (fun a => emb (ts a)) =
 Frame H M W (c.subst ts) (B.subst ts) (frame.subst ts) := by
 unfold Frame frameMatrix
 rw [blockSubst,liftedEmbedding,frameFieldsSubst]
 simp only [liftSubst,Term.subst,Sum.elim_inr]
theorem frameFieldsRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B frame parent payload counts : OTerm alpha) (j : alpha → beta) :
 (frameFields H M W c B frame parent payload counts).relabel j =
 frameFields H M W (c.relabel j) (B.relabel j) (frame.relabel j) (parent.relabel j) (payload.relabel j) (counts.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (frameFields H M W c B frame parent payload counts).subst (fun a => emb (.var (j a))) = _
 rw [frameFieldsSubst]
 simp only [← termRelabelAsSubst]
theorem frameRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B frame : OTerm alpha) (j : alpha → beta) :
 (Frame H M W c B frame).relabel j =
 Frame H M W (c.relabel j) (B.relabel j) (frame.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Frame H M W c B frame).subst (fun a => emb (.var (j a))) = _
 rw [frameSubst]
 simp only [← termRelabelAsSubst]
theorem lookupFieldsSubst {beta : Type} 
 (work count index frame : OTerm alpha) (ts : alpha → OTerm beta) :
 (lookupFields  work count index frame).subst (fun a => emb (ts a)) =
 lookupFields  (work.subst ts) (count.subst ts) (index.subst ts) (frame.subst ts) := by
 simp only [lookupFields,Below,conjunctionSubst,orderSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]
theorem agendaSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B work : OTerm alpha) (ts : alpha → OTerm beta) :
 (Agenda H M W c B work).subst (fun a => emb (ts a)) =
 Agenda H M W (c.subst ts) (B.subst ts) (work.subst ts) := by
 unfold Agenda agendaMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [lookupFieldsSubst,frameSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem agendaRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B work : OTerm alpha) (j : alpha → beta) :
 (Agenda H M W c B work).relabel j = Agenda H M W (c.relabel j) (B.relabel j) (work.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Agenda H M W c B work).subst (fun a => emb (.var (j a))) = _
 rw [agendaSubst]
 simp only [← termRelabelAsSubst]
theorem jobWitness (H : Program 1) (M W : Program 2) (c B job role typ typed rawJob raw parameter gamma weight : OTerm alpha) :
 (jobMatrix H M W c B job).subst (Sum.elim Term.var (fun i => emb (![role,typ,typed,rawJob,raw,parameter,gamma,weight] i))) =
 jobFields H M W c B job role typ typed rawJob raw parameter gamma weight := by
 have he : (Sum.elim Term.var (fun i => emb (![role,typ,typed,rawJob,raw,parameter,gamma,weight] i))) =
   (fun a => emb (Sum.elim Term.var ![role,typ,typed,rawJob,raw,parameter,gamma,weight] a)) := by funext a; cases a <;> rfl
 unfold jobMatrix
 rw [he]
 simp only [jobFieldsSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem frameWitness (H : Program 1) (M W : Program 2) (c B frame parent payload counts : OTerm alpha) :
 (frameMatrix H M W c B frame).subst (Sum.elim Term.var (fun i => emb (![parent,payload,counts] i))) =
 frameFields H M W c B frame parent payload counts := by
 have he : (Sum.elim Term.var (fun i => emb (![parent,payload,counts] i))) =
   (fun a => emb (Sum.elim Term.var ![parent,payload,counts] a)) := by funext a; cases a <;> rfl
 unfold frameMatrix
 rw [he]
 simp only [frameFieldsSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem agendaWitness (H : Program 1) (M W : Program 2) (c B work count index frame : OTerm alpha) :
 (agendaMatrix H M W c B work).subst (Sum.elim Term.var (fun i => emb (![count,index,frame] i))) =
 (lookupFields work count index frame).imp (Frame H M W c B frame) := by
 have he : (Sum.elim Term.var (fun i => emb (![count,index,frame] i))) =
   (fun a => emb (Sum.elim Term.var ![count,index,frame] a)) := by funext a; cases a <;> rfl
 unfold agendaMatrix
 rw [he]
 simp only [impSubst,lookupFieldsSubst,frameSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
