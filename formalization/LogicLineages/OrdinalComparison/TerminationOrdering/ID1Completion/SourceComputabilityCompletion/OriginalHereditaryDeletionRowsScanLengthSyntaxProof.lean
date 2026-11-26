module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthSyntaxProof
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
open OriginalHereditaryDeletionRows
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (Q : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (graph3 (scan Q) (.var (.inr 2)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (lengthGraph (count.relabel Sum.inl) (.var (.inr 2)))
def row (Q : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (rowBody Q count)
theorem rowSubst {beta : Type} (Q : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row Q count).subst (fun a => emb (ts a)) = row Q (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,lengthSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (Q : Program 2) (count : OTerm alpha) (j : alpha → beta) :
    (row Q count).relabel j = row Q (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row Q count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (Q : Program 2) (count input parameter out : OTerm alpha) :
    (rowBody Q count).subst (Sum.elim Term.var (fun i => emb (![input,parameter,out] i))) =
      (graph3 (scan Q) out count input parameter).imp (lengthGraph count out) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,parameter,out] i))) =
      (fun a => emb (Sum.elim Term.var ![input,parameter,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,lengthSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row Q count) (emb t) = row Q (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row Q count) = row Q (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (Q : Program 2) (count input parameter out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (graph3 (scan Q) out count input parameter))) :
    Nonempty (Derivation body Delta (lengthGraph count out)) := by
  have h := actualFiniteUniversalElimination body alpha 3 Delta (rowBody Q count)
    (fun i => emb (![input,parameter,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthSyntaxProof
