module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionSyntax
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
open UniformReturnDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open UniformReturnSyntax (frameSubst frameRename)
open OriginalContextInsertionSyntaxProof (blockSubst)
theorem completionSubst {beta : Type} (R : Program 2) (frame produced : OTerm alpha) (ts : alpha → OTerm beta) :
 (Completion R frame produced).subst (fun a => emb (ts a)) = Completion R (frame.subst ts) (produced.subst ts) := by
 unfold Completion matrix
 rw [blockSubst,liftedEmbedding,frameSubst]
 simp only [liftSubst,Term.subst,Sum.elim_inr]
theorem completionRename {beta : Type} (R : Program 2) (frame produced : OTerm alpha) (j : alpha → beta) :
 (Completion R frame produced).relabel j = Completion R (frame.relabel j) (produced.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Completion R frame produced).subst (fun a => emb (.var (j a))) = _
 rw [completionSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (R : Program 2) (frame produced value : OTerm alpha) :
 (matrix R frame produced).subst (Sum.elim Term.var (fun i => emb (![value] i))) = Framed R frame produced value := by
 have he : (Sum.elim Term.var (fun i => emb (![value] i))) =
   (fun a => emb (Sum.elim Term.var ![value] a)) := by funext a; cases a <;> rfl
 unfold matrix
 rw [he,frameSubst]
 simp only [witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem completionIntro (R : Program 2) (frame produced value : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Framed R frame produced value))) :
 Nonempty (Derivation body Delta (Completion R frame produced)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 1 Delta
   (matrix R frame produced) (fun i => emb (![value] i))
 rw [matrixWitness]
 exact h
theorem completionCases (R : Program 2) (frame produced : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Completion R frame produced)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (value : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (Framed R (frame.relabel j) (produced.relabel j) value)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let P := matrix R frame produced
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 1 Delta P psi h
 exact next (alpha ⊕ Fin 1) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionSyntax
