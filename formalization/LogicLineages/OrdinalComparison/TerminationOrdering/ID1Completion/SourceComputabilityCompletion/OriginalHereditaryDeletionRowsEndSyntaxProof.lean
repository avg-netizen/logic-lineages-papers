module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndSyntaxProof
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

def fields (count front value singleton out : OTerm alpha) : Formula alpha :=
  lengthGraph count front ⊓ (consGraph singleton value z ⊓
    graph2 InternalApplicationValidityStackAppend.append out front singleton)
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3))).imp
      (graph2 InternalRawListRecursion.lookup (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 3)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem fieldsSubst {beta : Type} (count front value singleton out : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields count front value singleton out).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (front.subst ts) (value.subst ts) (singleton.subst ts) (out.subst ts) := by
  simp only [fields,conjunctionSubst,lengthSubst,consGraph,graph2,programSubst,consTermSubst,emptySubst,zSubst]
@[simp] theorem fieldsRename {beta : Type} (count front value singleton out : OTerm alpha) (j : alpha → beta) :
    (fields count front value singleton out).relabel j =
      fields (count.relabel j) (front.relabel j) (value.relabel j) (singleton.relabel j) (out.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields count front value singleton out).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count front value singleton out : OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![front,value,singleton,out] i))) =
      (fields count front value singleton out).imp (graph2 InternalRawListRecursion.lookup value count out) := by
  have he : (Sum.elim Term.var (fun i => emb (![front,value,singleton,out] i))) =
      (fun a => emb (Sum.elim Term.var ![front,value,singleton,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count front value singleton out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields count front value singleton out))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value count out)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody count)
    (fun i => emb (![front,value,singleton,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndSyntaxProof
