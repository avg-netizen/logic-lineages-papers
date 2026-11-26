module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
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
open Continuation20261115.OriginalCodeDecoderTable
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def fields (count output index : OTerm alpha) : Formula alpha :=
  Below index count ⊓ graph1 OriginalCodeDecoderTable.zeros output count
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
    (graph2 InternalRawListRecursion.lookup z (.var (.inr 1)) (.var (.inr 0)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem fieldsSubst {beta : Type} (count output index : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields count output index).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (output.subst ts) (index.subst ts) := by
  simp only [fields,conjunctionSubst,Below,orderSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (count output index : OTerm alpha) (j : alpha → beta) :
    (fields count output index).relabel j =
      fields (count.relabel j) (output.relabel j) (index.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields count output index).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,zSubst,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count output index : OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![output,index] i))) =
      (fields count output index).imp
        (graph2 InternalRawListRecursion.lookup z index output) := by
  have he : (Sum.elim Term.var (fun i => emb (![output,index] i))) =
      (fun a => emb (Sum.elim Term.var ![output,index] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,zSubst,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count output index : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields count output index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) := by
  have h := actualFiniteUniversalElimination body alpha 2 Delta (rowBody count)
    (fun i => emb (![output,index] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
