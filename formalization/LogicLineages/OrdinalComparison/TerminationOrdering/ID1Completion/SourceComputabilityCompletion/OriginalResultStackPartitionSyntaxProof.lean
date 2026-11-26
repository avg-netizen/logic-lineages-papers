module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
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
open InternalListCodecSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def fields (count initialList suffix joined : OTerm alpha) : Formula alpha :=
 lengthGraph count initialList ⊓ graph2 InternalApplicationValidityStackAppend.append joined initialList suffix
def outputs (count initialList suffix joined : OTerm alpha) : Formula alpha :=
 graph2 OriginalClassContextAllPositionObserver.front initialList count joined ⊓
 graph2 InternalRawListRecursion.drop suffix count joined
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (outputs (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)
theorem fieldsSubst {beta : Type} (count initialList suffix joined : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields count initialList suffix joined).subst (fun a => emb (ts a)) =
 fields (count.subst ts) (initialList.subst ts) (suffix.subst ts) (joined.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (count initialList suffix joined : OTerm alpha) (j : alpha → beta) :
 (fields count initialList suffix joined).relabel j =
 fields (count.relabel j) (initialList.relabel j) (suffix.relabel j) (joined.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields count initialList suffix joined).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]
theorem outputsSubst {beta : Type} (count initialList suffix joined : OTerm alpha) (ts : alpha → OTerm beta) :
 (outputs count initialList suffix joined).subst (fun a => emb (ts a)) =
 outputs (count.subst ts) (initialList.subst ts) (suffix.subst ts) (joined.subst ts) := by
 simp only [outputs,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem outputsRename {beta : Type} (count initialList suffix joined : OTerm alpha) (j : alpha → beta) :
 (outputs count initialList suffix joined).relabel j =
 outputs (count.relabel j) (initialList.relabel j) (suffix.relabel j) (joined.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (outputs count initialList suffix joined).subst (fun a => emb (.var (j a))) = _
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
theorem rowBodyWitness (count initialList suffix joined : OTerm alpha) :
 (rowBody count).subst (Sum.elim Term.var (fun i => emb (![initialList,suffix,joined] i))) =
 (fields count initialList suffix joined).imp (outputs count initialList suffix joined) := by
 have he : (Sum.elim Term.var (fun i => emb (![initialList,suffix,joined] i))) =
   (fun a => emb (Sum.elim Term.var ![initialList,suffix,joined] a)) := by
   funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,outputsSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row count) = row (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count initialList suffix joined : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields count initialList suffix joined))) :
 Nonempty (Derivation body Delta (outputs count initialList suffix joined)) := by
 have h := actualFiniteUniversalElimination body alpha 3 Delta (rowBody count)
   (fun i => emb (![initialList,suffix,joined] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionSyntaxProof
