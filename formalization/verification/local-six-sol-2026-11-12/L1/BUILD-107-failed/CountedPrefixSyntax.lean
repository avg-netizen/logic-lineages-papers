module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (add addSubst impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def fields (count remaining code front suffix : OTerm alpha) : Formula alpha :=
 lengthGraph (add count remaining) code ⊓
 (graph2 OriginalClassContextAllPositionObserver.front front count code ⊓
  graph2 InternalRawListRecursion.drop suffix count code)
def outputs (count remaining code front suffix : OTerm alpha) : Formula alpha :=
 lengthGraph count front ⊓ (lengthGraph remaining suffix ⊓
 graph2 InternalApplicationValidityStackAppend.append code front suffix)
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (outputs (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)
theorem fieldsSubst {beta : Type} (count remaining code front suffix : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields count remaining code front suffix).subst (fun a => emb (ts a)) =
 fields (count.subst ts) (remaining.subst ts) (code.subst ts) (front.subst ts) (suffix.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,addSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem fieldsRename {beta : Type} (count remaining code front suffix : OTerm alpha) (j : alpha → beta) :
 (fields count remaining code front suffix).relabel j =
 fields (count.relabel j) (remaining.relabel j) (code.relabel j) (front.relabel j) (suffix.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields count remaining code front suffix).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]
theorem outputsSubst {beta : Type} (count remaining code front suffix : OTerm alpha) (ts : alpha → OTerm beta) :
 (outputs count remaining code front suffix).subst (fun a => emb (ts a)) =
 outputs (count.subst ts) (remaining.subst ts) (code.subst ts) (front.subst ts) (suffix.subst ts) := by
 simp only [outputs,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem outputsRename {beta : Type} (count remaining code front suffix : OTerm alpha) (j : alpha → beta) :
 (outputs count remaining code front suffix).relabel j =
 outputs (count.relabel j) (remaining.relabel j) (code.relabel j) (front.relabel j) (suffix.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (outputs count remaining code front suffix).subst (fun a => emb (.var (j a))) = _
 rw [outputsSubst]
 simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,outputsSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
 (row count).relabel j = row (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row count).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count remaining code front suffix : OTerm alpha) :
 (rowBody count).subst (Sum.elim Term.var (fun i => emb (![remaining,code,front,suffix] i))) =
 (fields count remaining code front suffix).imp (outputs count remaining code front suffix) := by
 have he : (Sum.elim Term.var (fun i => emb (![remaining,code,front,suffix] i))) =
   (fun a => emb (Sum.elim Term.var ![remaining,code,front,suffix] a)) := by
   funext a
   cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,outputsSubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
   Matrix.head_cons,Matrix.tail_cons]
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row count) = row (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count remaining code front suffix : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields count remaining code front suffix))) :
 Nonempty (Derivation body Delta (outputs count remaining code front suffix)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody count)
   (fun i => emb (![remaining,code,front,suffix] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
