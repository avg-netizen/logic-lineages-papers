module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
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

open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
def fields (gamma count i j a b upper lower left right : OTerm alpha) : Formula alpha :=
  lengthGraph count gamma ⊓ (Below i (suc j) ⊓ (Below (suc j) count ⊓
    (graph2 InternalRawListRecursion.lookup a i gamma ⊓
      (graph2 InternalRawListRecursion.lookup b (suc j) gamma ⊓
        (graph2 deleteAt upper (suc j) gamma ⊓ (graph2 deleteAt left i upper ⊓
          (graph2 deleteAt lower i gamma ⊓ graph2 deleteAt right j lower)))))))
def result (i j a b upper lower left right : OTerm alpha) : Formula alpha :=
  equal left right ⊓ (graph2 InternalRawListRecursion.lookup a i upper ⊓
    graph2 InternalRawListRecursion.lookup b j lower)
def rowBody (i : OTerm alpha) : Formula (alpha ⊕ Fin 9) :=
  (fields (.var (.inr 0)) (.var (.inr 1)) (i.relabel Sum.inl) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))
    (.var (.inr 7)) (.var (.inr 8))).imp
      (result (i.relabel Sum.inl) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
        (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)))
def row (i : OTerm alpha) : Formula alpha := allBlock (rowBody i)

theorem fieldsSubst {beta : Type} (gamma count i j a b upper lower left right : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields gamma count i j a b upper lower left right).subst (fun x => emb (ts x)) =
      fields (gamma.subst ts) (count.subst ts) (i.subst ts) (j.subst ts) (a.subst ts) (b.subst ts) (upper.subst ts) (lower.subst ts) (left.subst ts) (right.subst ts) := by
  simp only [fields,conjunctionSubst,lengthSubst,Below,orderSubst,sucSubst,equalSubst,
    graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem fieldsRename {beta : Type} (gamma count i j a b upper lower left right : OTerm alpha) (rho : alpha → beta) :
    (fields gamma count i j a b upper lower left right).relabel rho =
      fields (gamma.relabel rho) (count.relabel rho) (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) := by
  rw [formulaRelabelAsSubst]
  change (fields gamma count i j a b upper lower left right).subst (fun x => emb (.var (rho x))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem resultSubst {beta : Type} (i j a b upper lower left right : OTerm alpha) (ts : alpha → OTerm beta) :
    (result i j a b upper lower left right).subst (fun x => emb (ts x)) =
      result (i.subst ts) (j.subst ts) (a.subst ts) (b.subst ts) (upper.subst ts) (lower.subst ts) (left.subst ts) (right.subst ts) := by
  simp only [result,conjunctionSubst,lengthSubst,Below,orderSubst,sucSubst,equalSubst,
    graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem resultRename {beta : Type} (i j a b upper lower left right : OTerm alpha) (rho : alpha → beta) :
    (result i j a b upper lower left right).relabel rho =
      result (i.relabel rho) (j.relabel rho) (a.relabel rho) (b.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) := by
  rw [formulaRelabelAsSubst]
  change (result i j a b upper lower left right).subst (fun x => emb (.var (rho x))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]
theorem rowSubst {beta : Type} (i : OTerm alpha) (ts : alpha → OTerm beta) :
    (row i).subst (fun a => emb (ts a)) = row (i.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (i : OTerm alpha) (j : alpha → beta) :
    (row i).relabel j = row (i.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row i).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]
theorem rowBodyWitness (gamma count i j a b upper lower left right : OTerm alpha) :
    (rowBody i).subst (Sum.elim Term.var (fun k => emb (![gamma,count,j,a,b,upper,lower,left,right] k))) =
      (fields gamma count i j a b upper lower left right).imp (result i j a b upper lower left right) := by
  have he : (Sum.elim Term.var (fun k => emb (![gamma,count,j,a,b,upper,lower,left,right] k))) =
      (fun x => emb (Sum.elim Term.var ![gamma,count,j,a,b,upper,lower,left,right] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem rowInstantiate (i : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row i) (emb t) = row (i.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (i : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row i) = row (i.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (gamma count i j a b upper lower left right : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row i)))
    (hf : Nonempty (Derivation body Delta (fields gamma count i j a b upper lower left right))) :
    Nonempty (Derivation body Delta (result i j a b upper lower left right)) := by
  have h := actualFiniteUniversalElimination body alpha 9 Delta (rowBody i)
    (fun k => emb (![gamma,count,j,a,b,upper,lower,left,right] k)) hrow
  rw [rowBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionSyntaxProof
