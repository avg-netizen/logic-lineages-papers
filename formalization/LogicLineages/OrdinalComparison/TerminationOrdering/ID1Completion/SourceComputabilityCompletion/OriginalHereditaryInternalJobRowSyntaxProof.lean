module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowTargets
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowSyntaxProof
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
open OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalJobRow
theorem jobsSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (c B work : OTerm alpha) (ts : alpha → OTerm beta) :
 (Jobs H M W c B work).subst (fun a => emb (ts a)) =
 Jobs H M W (c.subst ts) (B.subst ts) (work.subst ts) := by
 unfold Jobs jobsMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [lookupFieldsSubst,jobSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem jobsRename {beta : Type} (H : Program 1) (M W : Program 2)
 (c B work : OTerm alpha) (j : alpha → beta) :
 (Jobs H M W c B work).relabel j = Jobs H M W (c.relabel j) (B.relabel j) (work.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Jobs H M W c B work).subst (fun a => emb (.var (j a))) = _
 rw [jobsSubst]
 simp only [← termRelabelAsSubst]
theorem jobsWitness (H : Program 1) (M W : Program 2) (c B work count index frame : OTerm alpha) :
 (jobsMatrix H M W c B work).subst (Sum.elim Term.var (fun i => emb (![count,index,frame] i))) =
 (lookupFields work count index frame).imp (Job H M W c B frame) := by
 have he : (Sum.elim Term.var (fun i => emb (![count,index,frame] i))) =
   (fun a => emb (Sum.elim Term.var ![count,index,frame] a)) := by funext a; cases a <;> rfl
 unfold jobsMatrix
 rw [he]
 simp only [impSubst,lookupFieldsSubst,jobSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowSyntaxProof
