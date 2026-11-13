module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
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
open VisitListCompletionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open PrefixFrameSyntax (frameSubst frameRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalQuotientComparisonSyntaxProof (orderSubst)
theorem completionSubst {beta : Type} (R : Program 2) (size tagged : OTerm alpha) (ts : alpha → OTerm beta) :
 (Completion R size tagged).subst (fun a => emb (ts a)) = Completion R (size.subst ts) (tagged.subst ts) := by
 unfold Completion completionMatrix
 rw [blockSubst,liftedEmbedding,conjunctionSubst]
 simp only [lengthSubst,frameSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem completionRename {beta : Type} (R : Program 2) (size tagged : OTerm alpha) (j : alpha → beta) :
 (Completion R size tagged).relabel j = Completion R (size.relabel j) (tagged.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Completion R size tagged).subst (fun a => emb (.var (j a))) = _
 rw [completionSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (R : Program 2) (size tagged count produced : OTerm alpha) :
 (completionMatrix R size tagged).subst (Sum.elim Term.var (fun i => emb (![count,produced] i))) =
 lengthGraph size produced ⊓ PrefixFrameDefinitions.PrefixFrame R tagged count produced := by
 have he : (Sum.elim Term.var (fun i => emb (![count,produced] i))) =
   (fun a => emb (Sum.elim Term.var ![count,produced] a)) := by funext a; cases a <;> rfl
 unfold completionMatrix
 rw [he,conjunctionSubst]
 simp only [lengthSubst,frameSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem completionIntro (R : Program 2) (size tagged count produced : OTerm alpha)
 (h : Nonempty (Derivation body Delta (lengthGraph size produced ⊓ PrefixFrameDefinitions.PrefixFrame R tagged count produced))) :
 Nonempty (Derivation body Delta (Completion R size tagged)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 2 Delta
   (completionMatrix R size tagged) (fun i => emb (![count,produced] i))
 rw [matrixWitness]
 exact h
theorem completionCases (R : Program 2) (size tagged : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Completion R size tagged)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count produced : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (lengthGraph (size.relabel j) produced ⊓ PrefixFrameDefinitions.PrefixFrame R (tagged.relabel j) count produced)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := completionMatrix R size tagged
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 2 Delta P psi h
 exact next (alpha ⊕ Fin 2) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0)) (.var (.inr 1))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem allSubst {beta : Type} (R : Program 2) (size jobs : OTerm alpha) (ts : alpha → OTerm beta) :
 (AllComplete R size jobs).subst (fun a => emb (ts a)) = AllComplete R (size.subst ts) (jobs.subst ts) := by
 unfold AllComplete allBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
   JobCompletionSyntax.completionSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem allRename {beta : Type} (R : Program 2) (size jobs : OTerm alpha) (j : alpha → beta) :
 (AllComplete R size jobs).relabel j = AllComplete R (size.relabel j) (jobs.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AllComplete R size jobs).subst (fun a => emb (.var (j a))) = _
 rw [allSubst]
 simp only [← termRelabelAsSubst]
theorem allWitness (R : Program 2) (size jobs index job : OTerm alpha) :
 (allBody R size jobs).subst (Sum.elim Term.var (fun i => emb (![index,job] i))) =
 (Below index size ⊓ graph2 InternalRawListRecursion.lookup job index jobs).imp
  (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job) := by
 have he : (Sum.elim Term.var (fun i => emb (![index,job] i))) =
   (fun a => emb (Sum.elim Term.var ![index,job] a)) := by funext a; cases a <;> rfl
 unfold allBody
 rw [he,impSubst]
 simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
   JobCompletionSyntax.completionSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem allApply (R : Program 2) (size jobs index job : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllComplete R size jobs)))
 (hf : Nonempty (Derivation body Delta (Below index size ⊓ graph2 InternalRawListRecursion.lookup job index jobs))) :
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (allBody R size jobs)
   (fun i => emb (![index,job] i)) ha
 rw [allWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
