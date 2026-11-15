module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
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
open Continuation20261115.OriginalCodeDecoderTable
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (n : Nat) (count : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (graph2 (nextRow n) (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0))).imp
    (lengthGraph (suc (count.relabel Sum.inl)) (.var (.inr 1)))
def row (n : Nat) (count : OTerm alpha) : Formula alpha := allBlock (rowBody n count)
theorem rowSubst {beta : Type} (n : Nat) (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row n count).subst (fun a => emb (ts a)) = row n (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graph2,programSubst,consTermSubst,emptySubst,lengthSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (n : Nat) (count : OTerm alpha) (j : alpha → beta) :
    (row n count).relabel j = row n (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row n count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (n : Nat) (count previous out : OTerm alpha) :
    (rowBody n count).subst (Sum.elim Term.var (fun i => emb (![previous,out] i))) =
      (graph2 (nextRow n) out count previous).imp (lengthGraph (suc count) out) := by
  have he : (Sum.elim Term.var (fun i => emb (![previous,out] i))) =
      (fun a => emb (Sum.elim Term.var ![previous,out] a)) := by
    funext a
    cases a <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [graph2,programSubst,consTermSubst,emptySubst,lengthSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (n : Nat) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row n count) (emb t) = row n (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (n : Nat) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row n count) = row n (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (n : Nat) (count previous out : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n count)))
    (hf : Nonempty (Derivation body Delta (graph2 (nextRow n) out count previous))) :
    Nonempty (Derivation body Delta (lengthGraph (suc count) out)) := by
  have h := actualFiniteUniversalElimination body alpha 2 Delta (rowBody n count)
    (fun i => emb (![previous,out] i)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
