module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentDefinitions
open Runtime.JobFrameSyntax (frameSubst)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem contentSubst {beta : Type} (R : Program 2) (job value : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (Content R job value).subst (fun a => emb (ts a)) =
 Content R (job.subst ts) (value.subst ts) := by
 simp only [Content,graph1,programSubst,consTermSubst,emptySubst]
theorem allContentSubst {beta : Type} (R : Program 2) (job : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (AllFramedContent R job).subst (fun a => emb (ts a)) =
 AllFramedContent R (job.subst ts) := by
 unfold AllFramedContent contentMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [frameSubst,contentSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem allContentRename {beta : Type} (R : Program 2) (job : OTerm alpha)
 (j : alpha → beta) :
 (AllFramedContent R job).relabel j = AllFramedContent R (job.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AllFramedContent R job).subst (fun a => emb (.var (j a))) = _
 rw [allContentSubst]
 simp only [← termRelabelAsSubst]
theorem contentWitness (R : Program 2) (job count value : OTerm alpha) :
 (contentMatrix R job).subst (Sum.elim Term.var (fun i => emb (![count,value] i))) =
 (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value).imp
   (Content R job value) := by
 have he : (Sum.elim Term.var (fun i => emb (![count,value] i))) =
   (fun a => emb (Sum.elim Term.var ![count,value] a)) := by
   funext a
   cases a <;> rfl
 unfold contentMatrix
 rw [he,impSubst]
 simp only [frameSubst,contentSubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one]
theorem contentApply (R : Program 2) (job count value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (AllFramedContent R job)))
 (hf : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (contentMatrix R job)
   (fun i => emb (![count,value] i)) hc
 rw [contentWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
