module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
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

def fields (n : Nat) (fuel bound previous next index : OTerm alpha) : Formula alpha :=
  (graph2 (OriginalCodeDecoderTable.tableProgram n) previous fuel bound ⊓
    graph2 (OriginalCodeDecoderTable.tableProgram n) next (suc fuel) bound) ⊓
  (Below index (suc bound) ⊓ graph2 InternalRawListRecursion.lookup (suc z) index previous)
def rowBody (n : Nat) (fuel : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (fields n (fuel.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3))).imp
      (graph2 InternalRawListRecursion.lookup (suc z) (.var (.inr 3)) (.var (.inr 2)))
def row (n : Nat) (fuel : OTerm alpha) : Formula alpha := allBlock (rowBody n fuel)

theorem fieldsSubst {beta : Type} (n : Nat) (fuel bound previous next index : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields n fuel bound previous next index).subst (fun a => emb (ts a)) =
      fields n (fuel.subst ts) (bound.subst ts) (previous.subst ts) (next.subst ts) (index.subst ts) := by
  simp only [fields,conjunctionSubst,Below,orderSubst,sucSubst,zSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (n : Nat) (fuel bound previous next index : OTerm alpha) (j : alpha → beta) :
    (fields n fuel bound previous next index).relabel j =
      fields n (fuel.relabel j) (bound.relabel j) (previous.relabel j) (next.relabel j) (index.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n fuel bound previous next index).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (n : Nat) (fuel : OTerm alpha) (ts : alpha → OTerm beta) :
    (row n fuel).subst (fun a => emb (ts a)) = row n (fuel.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,sucSubst,zSubst,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (n : Nat) (fuel : OTerm alpha) (j : alpha → beta) :
    (row n fuel).relabel j = row n (fuel.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row n fuel).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (n : Nat) (fuel bound previous next index : OTerm alpha) :
    (rowBody n fuel).subst
      (Sum.elim Term.var (fun i => emb (![bound,previous,next,index] i))) =
      (fields n fuel bound previous next index).imp
        (graph2 InternalRawListRecursion.lookup (suc z) index next) := by
  have he : (Sum.elim Term.var (fun i => emb (![bound,previous,next,index] i))) =
      (fun a => emb (Sum.elim Term.var ![bound,previous,next,index] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,sucSubst,zSubst,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (n : Nat) (fuel : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row n fuel) (emb t) = row n (fuel.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (n : Nat) (fuel : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row n fuel) = row n (fuel.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (n : Nat) (fuel bound previous next index : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n fuel)))
    (hf : Nonempty (Derivation body Delta (fields n fuel bound previous next index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index next)) := by
  have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody n fuel)
    (fun i => emb (![bound,previous,next,index] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
