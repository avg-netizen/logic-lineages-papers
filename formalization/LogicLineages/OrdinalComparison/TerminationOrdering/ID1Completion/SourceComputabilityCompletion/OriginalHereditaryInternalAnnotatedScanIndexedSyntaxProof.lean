module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
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
open OriginalHereditaryInternalAnnotatedScanDefinitions
open OriginalHereditaryAnnotatedExpansion (scan)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def fields (count role typ raw jobs output cutoff value : OTerm alpha) : Formula alpha :=
  Below cutoff count ⊓ (graph5 scan output count role typ raw jobs ⊓
    graph2 InternalRawListRecursion.lookup value cutoff output)
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
      (graph5 cell (.var (.inr 6)) (.var (.inr 5)) (.var (.inr 0)) (.var (.inr 1))
        (.var (.inr 2)) (.var (.inr 3)))

def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem fieldsSubst {beta : Type} (count role typ raw jobs output cutoff value : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields count role typ raw jobs output cutoff value).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (role.subst ts) (typ.subst ts) (raw.subst ts) (jobs.subst ts) (output.subst ts) (cutoff.subst ts) (value.subst ts) := by
  simp only [fields,conjunctionSubst,Below,orderSubst,graph5,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (count role typ raw jobs output cutoff value : OTerm alpha) (j : alpha → beta) :
    (fields count role typ raw jobs output cutoff value).relabel j =
      fields (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j) (output.relabel j) (cutoff.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields count role typ raw jobs output cutoff value).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph5,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count role typ raw jobs output cutoff value : OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![role,typ,raw,jobs,output,cutoff,value] i))) =
      (fields count role typ raw jobs output cutoff value).imp
        (graph5 cell value cutoff role typ raw jobs) := by
  have he : (Sum.elim Term.var (fun i => emb (![role,typ,raw,jobs,output,cutoff,value] i))) =
      (fun a => emb (Sum.elim Term.var ![role,typ,raw,jobs,output,cutoff,value] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph5,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count role typ raw jobs output cutoff value : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields count role typ raw jobs output cutoff value))) :
    Nonempty (Derivation body Delta (graph5 cell value cutoff role typ raw jobs)) := by
  have h := actualFiniteUniversalElimination body alpha 7 Delta (rowBody count)
    (fun i => emb (![role,typ,raw,jobs,output,cutoff,value] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
