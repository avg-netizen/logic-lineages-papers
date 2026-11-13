module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthSyntax
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

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalQuotientComparisonSyntaxProof (orderSubst)

open InternalTagArithmeticSyntaxProof (bindTerm bindEmbedding nextTerm nextEmbedding)
def fields (F : Program 1) (size jobs tagged : OTerm alpha) : Formula alpha :=
 lengthGraph size jobs ⊓ graph1 (InternalListMap.map (k := 0) F) tagged jobs
def rowBody (F : Program 1) (size : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields F (size.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
 (lengthGraph (size.relabel Sum.inl) (.var (.inr 1)))
def row (F : Program 1) (size : OTerm alpha) : Formula alpha := allBlock (rowBody F size)
theorem fieldsSubst {beta : Type} (F : Program 1) (size jobs tagged : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields F size jobs tagged).subst (fun a => emb (ts a)) = fields F (size.subst ts) (jobs.subst ts) (tagged.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,graph1,programSubst,consTermSubst,emptySubst]
theorem fieldsRename {beta : Type} (F : Program 1) (size jobs tagged : OTerm alpha) (j : alpha → beta) :
 (fields F size jobs tagged).relabel j = fields F (size.relabel j) (jobs.relabel j) (tagged.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields F size jobs tagged).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (F : Program 1) (size : OTerm alpha) (ts : alpha → OTerm beta) :
 (row F size).subst (fun a => emb (ts a)) = row F (size.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,lengthSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (F : Program 1) (size : OTerm alpha) (j : alpha → beta) :
 (row F size).relabel j = row F (size.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row F size).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (F : Program 1) (size jobs tagged : OTerm alpha) :
 (rowBody F size).subst (Sum.elim Term.var (fun i => emb (![jobs,tagged] i))) =
 (fields F size jobs tagged).imp (lengthGraph size tagged) := by
 have he : (Sum.elim Term.var (fun i => emb (![jobs,tagged] i))) =
   (fun a => emb (Sum.elim Term.var ![jobs,tagged] a)) := by funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,lengthSubst,witnessLift,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
theorem rowApply (F : Program 1) (size jobs tagged : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row F size)))
 (hf : Nonempty (Derivation body Delta (fields F size jobs tagged))) :
 Nonempty (Derivation body Delta (lengthGraph size tagged)) := by
 have h := actualFiniteUniversalElimination body alpha 2 Delta (rowBody F size)
   (fun i => emb (![jobs,tagged] i)) hr
 rw [bodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
theorem rowInstantiate (F : Program 1) (size : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row F size) (emb t) = row F (size.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (F : Program 1) (size : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row F size) = row F (size.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthSyntax
