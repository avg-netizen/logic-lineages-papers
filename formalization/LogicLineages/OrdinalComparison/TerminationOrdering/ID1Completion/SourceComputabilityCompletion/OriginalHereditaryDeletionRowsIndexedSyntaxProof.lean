module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedSyntaxProof
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
open OriginalHereditaryDeletionRows
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def fields (Q : Program 2) (count input parameter output cutoff value : OTerm alpha) : Formula alpha :=
  Below cutoff count ⊓ (graph3 (scan Q) output count input parameter ⊓
    graph2 InternalRawListRecursion.lookup value cutoff output)
def rowBody (Q : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields Q (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
      (graph3 (observation Q) (.var (.inr 4)) (.var (.inr 3)) (.var (.inr 0)) (.var (.inr 1)))
def row (Q : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (rowBody Q count)

theorem fieldsSubst {beta : Type} (Q : Program 2) (count input parameter output cutoff value : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields Q count input parameter output cutoff value).subst (fun a => emb (ts a)) =
      fields Q (count.subst ts) (input.subst ts) (parameter.subst ts) (output.subst ts) (cutoff.subst ts) (value.subst ts) := by
  simp only [fields,conjunctionSubst,Below,orderSubst,graph3,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (Q : Program 2) (count input parameter output cutoff value : OTerm alpha) (j : alpha → beta) :
    (fields Q count input parameter output cutoff value).relabel j =
      fields Q (count.relabel j) (input.relabel j) (parameter.relabel j) (output.relabel j) (cutoff.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields Q count input parameter output cutoff value).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (Q : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row Q count).subst (fun a => emb (ts a)) = row Q (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph3,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (Q : Program 2) (count : OTerm alpha) (j : alpha → beta) :
    (row Q count).relabel j = row Q (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row Q count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (Q : Program 2) (count input parameter output cutoff value : OTerm alpha) :
    (rowBody Q count).subst
      (Sum.elim Term.var (fun i => emb (![input,parameter,output,cutoff,value] i))) =
      (fields Q count input parameter output cutoff value).imp
        (graph3 (observation Q) value cutoff input parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter,output,cutoff,value] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter,output,cutoff,value] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph3,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row Q count) (emb t) = row Q (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row Q count) = row Q (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (Q : Program 2) (count input parameter output cutoff value : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q count input parameter output cutoff value))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody Q count)
    (fun i => emb (![input,parameter,output,cutoff,value] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedSyntaxProof
