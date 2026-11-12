module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionSyntaxProof
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

def fields (count gamma cutoff deleted d : OTerm alpha) : Formula alpha :=
  lengthGraph count gamma ⊓ (Below cutoff count ⊓
    (graph2 deleteAt deleted cutoff gamma ⊓ graph2 InternalRawListRecursion.lookup d cutoff gamma))
def rowBody (cutoff : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields (.var (.inr 0)) (.var (.inr 1)) (cutoff.relabel Sum.inl)
    (.var (.inr 2)) (.var (.inr 3))).imp
      (Insert (.var (.inr 3)) (cutoff.relabel Sum.inl) (.var (.inr 2)) (.var (.inr 1)))
def row (cutoff : OTerm alpha) : Formula alpha := allBlock (rowBody cutoff)

theorem fieldsSubst {beta : Type} (count gamma cutoff deleted d : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields count gamma cutoff deleted d).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (gamma.subst ts) (cutoff.subst ts) (deleted.subst ts) (d.subst ts) := by
  simp only [fields,conjunctionSubst,lengthSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (count gamma cutoff deleted d : OTerm alpha) (j : alpha → beta) :
    (fields count gamma cutoff deleted d).relabel j =
      fields (count.relabel j) (gamma.relabel j) (cutoff.relabel j) (deleted.relabel j) (d.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields count gamma cutoff deleted d).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (cutoff : OTerm alpha) (ts : alpha → OTerm beta) :
    (row cutoff).subst (fun a => emb (ts a)) = row (cutoff.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,insertSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (cutoff : OTerm alpha) (j : alpha → beta) :
    (row cutoff).relabel j = row (cutoff.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row cutoff).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count gamma cutoff deleted d : OTerm alpha) :
    (rowBody cutoff).subst
      (Sum.elim Term.var (fun i => emb (![count,gamma,deleted,d] i))) =
      (fields count gamma cutoff deleted d).imp (Insert d cutoff deleted gamma) := by
  have he : (Sum.elim Term.var (fun i => emb (![count,gamma,deleted,d] i))) =
      (fun a => emb (Sum.elim Term.var ![count,gamma,deleted,d] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,insertSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (cutoff : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row cutoff) (emb t) = row (cutoff.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (cutoff : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row cutoff) = row (cutoff.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count gamma cutoff deleted d : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hf : Nonempty (Derivation body Delta (fields count gamma cutoff deleted d))) :
    Nonempty (Derivation body Delta (Insert d cutoff deleted gamma)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody cutoff)
    (fun i => emb (![count,gamma,deleted,d] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionSyntaxProof
