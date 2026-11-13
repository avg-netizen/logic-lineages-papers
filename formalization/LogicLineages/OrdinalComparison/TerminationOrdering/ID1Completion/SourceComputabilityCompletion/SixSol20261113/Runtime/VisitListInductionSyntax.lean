module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionSyntax
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
open InternalOriginalOrderSyntaxProof (orderSubst)
open VisitListCompletionSyntax
open InternalTagArithmeticSyntaxProof (bindTerm bindEmbedding nextTerm nextEmbedding)
def fields (R : Program 2) (size jobs tagged : OTerm alpha) : Formula alpha :=
 lengthGraph size jobs ⊓ (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs ⊓ AllComplete R size jobs)
def rowBody (R : Program 2) (size : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields R (size.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
 (Completion R (size.relabel Sum.inl) (.var (.inr 1)))
def row (R : Program 2) (size : OTerm alpha) : Formula alpha := allBlock (rowBody R size)
theorem fieldsSubst {beta : Type} (R : Program 2) (size jobs tagged : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields R size jobs tagged).subst (fun a => emb (ts a)) = fields R (size.subst ts) (jobs.subst ts) (tagged.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,graph1,programSubst,consTermSubst,emptySubst,allSubst]
theorem fieldsRename {beta : Type} (R : Program 2) (size jobs tagged : OTerm alpha) (j : alpha → beta) :
 (fields R size jobs tagged).relabel j = fields R (size.relabel j) (jobs.relabel j) (tagged.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields R size jobs tagged).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (R : Program 2) (size : OTerm alpha) (ts : alpha → OTerm beta) :
 (row R size).subst (fun a => emb (ts a)) = row R (size.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,completionSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (R : Program 2) (size : OTerm alpha) (j : alpha → beta) :
 (row R size).relabel j = row R (size.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row R size).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (R : Program 2) (size jobs tagged : OTerm alpha) :
 (rowBody R size).subst (Sum.elim Term.var (fun i => emb (![jobs,tagged] i))) =
 (fields R size jobs tagged).imp (Completion R size tagged) := by
 have he : (Sum.elim Term.var (fun i => emb (![jobs,tagged] i))) =
   (fun a => emb (Sum.elim Term.var ![jobs,tagged] a)) := by funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,completionSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem rowApply (R : Program 2) (size jobs tagged : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R size jobs tagged))) :
 Nonempty (Derivation body Delta (Completion R size tagged)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (rowBody R size)
   (fun i => emb (![jobs,tagged] i)) hr
 rw [bodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
theorem rowInstantiate (R : Program 2) (size : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row R size) (emb t) = row R (size.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (R : Program 2) (size : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row R size) = row R (size.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionSyntax
