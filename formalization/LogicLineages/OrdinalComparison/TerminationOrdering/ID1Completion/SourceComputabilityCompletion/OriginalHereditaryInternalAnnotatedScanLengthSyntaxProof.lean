module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
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
open OriginalHereditaryAnnotatedExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (graph5 scan (.var (.inr 4)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
    (lengthGraph (count.relabel Sum.inl) (.var (.inr 4)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graph5,programSubst,consTermSubst,emptySubst,lengthSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count role typ raw jobs out : OTerm alpha) :
    (rowBody count).subst (Sum.elim Term.var (fun i => emb (![role,typ,raw,jobs,out] i))) =
      (graph5 scan out count role typ raw jobs).imp (lengthGraph count out) := by
  have he : (Sum.elim Term.var (fun i => emb (![role,typ,raw,jobs,out] i))) =
      (fun a => emb (Sum.elim Term.var ![role,typ,raw,jobs,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [graph5,programSubst,consTermSubst,emptySubst,lengthSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count role typ raw jobs out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (graph5 scan out count role typ raw jobs))) :
    Nonempty (Derivation body Delta (lengthGraph count out)) := by
  have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody count)
    (fun i => emb (![role,typ,raw,jobs,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthSyntaxProof
