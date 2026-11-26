module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
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
open SixSol20261112.Runtime.FramedCompletionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem geometrySubst {beta : Type} (job value suffix old frame work input pushed output : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (geometry job value suffix old frame work input pushed output).subst (fun a => emb (ts a)) =
 geometry (job.subst ts) (value.subst ts) (suffix.subst ts) (old.subst ts) (frame.subst ts)
  (work.subst ts) (input.subst ts) (pushed.subst ts) (output.subst ts) := by
 simp only [geometry,numeralSubst,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem geometryRename {beta : Type} (job value suffix old frame work input pushed output : OTerm alpha)
 (j : alpha → beta) :
 (geometry job value suffix old frame work input pushed output).relabel j =
 geometry (job.relabel j) (value.relabel j) (suffix.relabel j) (old.relabel j) (frame.relabel j)
  (work.relabel j) (input.relabel j) (pushed.relabel j) (output.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (geometry job value suffix old frame work input pushed output).subst (fun a => emb (.var (j a))) = _
 rw [geometrySubst]
 simp only [← termRelabelAsSubst]
theorem frameSubst {beta : Type} (R : Program 2) (job count value : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (Framed R job count value).subst (fun a => emb (ts a)) =
 Framed R (job.subst ts) (count.subst ts) (value.subst ts) := by
 unfold Framed framedBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [geometrySubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem frameRename {beta : Type} (R : Program 2) (job count value : OTerm alpha)
 (j : alpha → beta) :
 (Framed R job count value).relabel j =
 Framed R (job.relabel j) (count.relabel j) (value.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Framed R job count value).subst (fun a => emb (.var (j a))) = _
 rw [frameSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (R : Program 2) (job count value suffix old frame work input pushed output : OTerm alpha) :
 (framedBody R job count value).subst (Sum.elim Term.var (fun i => emb (![suffix,old,frame,work,input,pushed,output] i))) =
 (geometry job value suffix old frame work input pushed output).imp
  (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input) := by
 have he : (Sum.elim Term.var (fun i => emb (![suffix,old,frame,work,input,pushed,output] i))) =
   (fun a => emb (Sum.elim Term.var ![suffix,old,frame,work,input,pushed,output] a)) := by
   funext a
   cases a <;> rfl
 unfold framedBody
 rw [he,impSubst]
 simp only [geometrySubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
   Matrix.head_cons,Matrix.tail_cons]
 rfl
theorem frameApply (R : Program 2) (job count value suffix old frame work input pushed output : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Framed R job count value)))
 (hg : Nonempty (Derivation body Delta (geometry job value suffix old frame work input pushed output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)) := by
 have h := actualFiniteUniversalElimination body alpha 7 Delta (framedBody R job count value)
   (fun i => emb (![suffix,old,frame,work,input,pushed,output] i)) hf
 rw [bodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hg⟩ := hg
 exact ⟨Derivation.implicationElimination h hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
