module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
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

def fields (n : Nat) (count previous output cutoff value : OTerm alpha) : Formula alpha :=
  Below cutoff (suc count) ⊓ (graph2 (nextRow n) output count previous ⊓
    graph2 InternalRawListRecursion.lookup value cutoff output)
def rowBody (n : Nat) (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields n (count.relabel Sum.inl) (.var (.inr 0))
    (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
      (graph2 (OriginalCodeDecoderStep.step n) (.var (.inr 3)) (.var (.inr 0)) (.var (.inr 2)))
def row (n : Nat) (count : OTerm alpha) : Formula alpha := allBlock (rowBody n count)

theorem fieldsSubst {beta : Type} (n : Nat) (count previous output cutoff value : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields n count previous output cutoff value).subst (fun a => emb (ts a)) =
      fields n (count.subst ts) (previous.subst ts) (output.subst ts) (cutoff.subst ts) (value.subst ts) := by
  simp only [fields,conjunctionSubst,Below,orderSubst,sucSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (n : Nat) (count previous output cutoff value : OTerm alpha) (j : alpha → beta) :
    (fields n count previous output cutoff value).relabel j =
      fields n (count.relabel j) (previous.relabel j) (output.relabel j) (cutoff.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n count previous output cutoff value).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (n : Nat) (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row n count).subst (fun a => emb (ts a)) = row n (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (n : Nat) (count : OTerm alpha) (j : alpha → beta) :
    (row n count).relabel j = row n (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row n count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (n : Nat) (count previous output cutoff value : OTerm alpha) :
    (rowBody n count).subst
      (Sum.elim Term.var (fun i => emb (![previous,output,cutoff,value] i))) =
      (fields n count previous output cutoff value).imp
        (graph2 (OriginalCodeDecoderStep.step n) value previous cutoff) := by
  have he : (Sum.elim Term.var (fun i => emb (![previous,output,cutoff,value] i))) =
      (fun a => emb (Sum.elim Term.var ![previous,output,cutoff,value] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (n : Nat) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row n count) (emb t) = row n (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (n : Nat) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row n count) = row n (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (n : Nat) (count previous output cutoff value : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n count)))
    (hf : Nonempty (Derivation body Delta (fields n count previous output cutoff value))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous cutoff)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody n count)
    (fun i => emb (![previous,output,cutoff,value] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
