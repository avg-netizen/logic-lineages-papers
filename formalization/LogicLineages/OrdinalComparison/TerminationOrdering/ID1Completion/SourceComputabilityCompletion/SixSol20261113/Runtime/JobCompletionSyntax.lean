module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
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
open JobFrameSyntax (frameSubst frameRename)
open OriginalContextInsertionSyntaxProof (blockSubst)
theorem completionSubst {beta : Type} (R : Program 2) (job : OTerm alpha) (ts : alpha → OTerm beta) :
 (Completion R job).subst (fun a => emb (ts a)) = Completion R (job.subst ts) := by
 unfold Completion completionMatrix
 rw [blockSubst,liftedEmbedding,frameSubst]
 simp only [liftSubst,Term.subst,Sum.elim_inr]
theorem completionRename {beta : Type} (R : Program 2) (job : OTerm alpha) (j : alpha → beta) :
 (Completion R job).relabel j = Completion R (job.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Completion R job).subst (fun a => emb (.var (j a))) = _
 rw [completionSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (R : Program 2) (job count value : OTerm alpha) :
 (completionMatrix R job).subst (Sum.elim Term.var (fun i => emb (![count,value] i))) = Framed R job count value := by
 have he : (Sum.elim Term.var (fun i => emb (![count,value] i))) =
   (fun a => emb (Sum.elim Term.var ![count,value] a)) := by funext a; cases a <;> rfl
 unfold completionMatrix
 rw [he,frameSubst]
 simp only [witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem completionIntro (R : Program 2) (job count value : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Framed R job count value))) :
 Nonempty (Derivation body Delta (Completion R job)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 2 Delta
   (completionMatrix R job) (fun i => emb (![count,value] i))
 rw [matrixWitness]
 exact h
theorem completionCases (R : Program 2) (job : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Completion R job)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count value : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (Framed R (job.relabel j) count value)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := completionMatrix R job
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 2 Delta P psi h
 exact next (alpha ⊕ Fin 2) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0)) (.var (.inr 1))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
