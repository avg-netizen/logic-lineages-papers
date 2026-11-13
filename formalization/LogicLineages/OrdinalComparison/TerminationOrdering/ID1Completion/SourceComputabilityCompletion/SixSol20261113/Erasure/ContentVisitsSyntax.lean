module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
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
open ContentVisitsDefinitions
open Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open PrefixFrameSyntax (frameSubst frameRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalQuotientComparisonSyntaxProof (orderSubst)
theorem countedSubst {beta : Type} (R : Program 2) (tagged produced : OTerm alpha) (ts : alpha → OTerm beta) :
 (Counted R tagged produced).subst (fun a => emb (ts a)) = Counted R (tagged.subst ts) (produced.subst ts) := by
 unfold Counted countMatrix
 rw [blockSubst,liftedEmbedding]
 simp only [frameSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem countedRename {beta : Type} (R : Program 2) (tagged produced : OTerm alpha) (j : alpha → beta) :
 (Counted R tagged produced).relabel j = Counted R (tagged.relabel j) (produced.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Counted R tagged produced).subst (fun a => emb (.var (j a))) = _
 rw [countedSubst]
 simp only [← termRelabelAsSubst]
theorem countWitness (R : Program 2) (tagged produced count : OTerm alpha) :
 (countMatrix R tagged produced).subst (Sum.elim Term.var (fun _ : Fin 1 => emb count)) =
 PrefixFrameDefinitions.PrefixFrame R tagged count produced := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb count)) =
   (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => count) a)) := by funext a; cases a <;> rfl
 unfold countMatrix
 rw [he,frameSubst]
 simp only [witnessLift,Term.subst,Sum.elim_inr]
theorem countedIntro (R : Program 2) (tagged produced count : OTerm alpha)
 (h : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 1 Delta
   (countMatrix R tagged produced) (fun _ => emb count)
 rw [countWitness]
 exact h
theorem countedCases (R : Program 2) (tagged produced : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Counted R tagged produced)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (PrefixFrameDefinitions.PrefixFrame R (tagged.relabel j) count (produced.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := countMatrix R tagged produced
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 1 Delta P psi h
 exact next (alpha ⊕ Fin 1) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem allSubst {beta : Type} (R : Program 2) (size jobs : OTerm alpha) (ts : alpha → OTerm beta) :
 (AllContent R size jobs).subst (fun a => emb (ts a)) = AllContent R (size.subst ts) (jobs.subst ts) := by
 unfold AllContent allBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
   FramedContentSyntax.allContentSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem allRename {beta : Type} (R : Program 2) (size jobs : OTerm alpha) (j : alpha → beta) :
 (AllContent R size jobs).relabel j = AllContent R (size.relabel j) (jobs.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AllContent R size jobs).subst (fun a => emb (.var (j a))) = _
 rw [allSubst]
 simp only [← termRelabelAsSubst]
theorem allWitness (R : Program 2) (size jobs index job : OTerm alpha) :
 (allBody R size jobs).subst (Sum.elim Term.var (fun i => emb (![index,job] i))) =
 (Below index size ⊓ graph2 InternalRawListRecursion.lookup job index jobs).imp
  (FramedContentDefinitions.AllFramedContent R job) := by
 have he : (Sum.elim Term.var (fun i => emb (![index,job] i))) =
   (fun a => emb (Sum.elim Term.var ![index,job] a)) := by funext a; cases a <;> rfl
 unfold allBody
 rw [he,impSubst]
 simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
   FramedContentSyntax.allContentSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem allApply (R : Program 2) (size jobs index job : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (Below index size ⊓ graph2 InternalRawListRecursion.lookup job index jobs))) :
 Nonempty (Derivation body Delta (FramedContentDefinitions.AllFramedContent R job)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (allBody R size jobs)
   (fun i => emb (![index,job] i)) ha
 rw [allWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
