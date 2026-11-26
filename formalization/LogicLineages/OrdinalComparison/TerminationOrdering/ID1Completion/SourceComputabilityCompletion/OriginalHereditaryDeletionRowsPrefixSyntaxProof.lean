module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixSyntaxProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def fields (count front cutoff suffix out value : OTerm alpha) : Formula alpha :=
  lengthGraph count front ⊓ (Below cutoff count ⊓
    (graph2 InternalApplicationValidityStackAppend.append out front suffix ⊓
      graph2 InternalRawListRecursion.lookup value cutoff front))
def rowBody (cutoff : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields (.var (.inr 0)) (.var (.inr 1)) (cutoff.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
      (graph2 InternalRawListRecursion.lookup (.var (.inr 4)) (cutoff.relabel Sum.inl) (.var (.inr 3)))
def row (cutoff : OTerm alpha) : Formula alpha := allBlock (rowBody cutoff)

theorem fieldsSubst {beta : Type} (count front cutoff suffix out value : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields count front cutoff suffix out value).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (front.subst ts) (cutoff.subst ts) (suffix.subst ts) (out.subst ts) (value.subst ts) := by
  simp only [fields,conjunctionSubst,lengthSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (count front cutoff suffix out value : OTerm alpha) (j : alpha → beta) :
    (fields count front cutoff suffix out value).relabel j =
      fields (count.relabel j) (front.relabel j) (cutoff.relabel j) (suffix.relabel j) (out.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields count front cutoff suffix out value).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (cutoff : OTerm alpha) (ts : alpha → OTerm beta) :
    (row cutoff).subst (fun a => emb (ts a)) = row (cutoff.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (cutoff : OTerm alpha) (j : alpha → beta) :
    (row cutoff).relabel j = row (cutoff.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row cutoff).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count front cutoff suffix out value : OTerm alpha) :
    (rowBody cutoff).subst
      (Sum.elim Term.var (fun i => emb (![count,front,suffix,out,value] i))) =
      (fields count front cutoff suffix out value).imp
        (graph2 InternalRawListRecursion.lookup value cutoff out) := by
  have he : (Sum.elim Term.var (fun i => emb (![count,front,suffix,out,value] i))) =
      (fun a => emb (Sum.elim Term.var ![count,front,suffix,out,value] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (cutoff : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row cutoff) (emb t) = row (cutoff.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (cutoff : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row cutoff) = row (cutoff.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count front cutoff suffix out value : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hf : Nonempty (Derivation body Delta (fields count front cutoff suffix out value))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff out)) := by
  have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody cutoff)
    (fun i => emb (![count,front,suffix,out,value] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixSyntaxProof
