module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalHereditaryBudgetSumBound
open InternalMultiplicationLawsProof (mul mulSubst)
open InternalBetaDivisionSyntaxProof (mulRelabel)
theorem cellFieldsSubst {beta : Type} (count jobs branching index child value : OTerm alpha) (ts : alpha → OTerm beta) :
 (cellFields count jobs branching index child value).subst (fun a => emb (ts a)) =
 cellFields (count.subst ts) (jobs.subst ts) (branching.subst ts) (index.subst ts) (child.subst ts) (value.subst ts) := by
 simp only [cellFields,Below,conjunctionSubst,orderSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem cellsSubst {beta : Type} (count jobs branching cap : OTerm alpha) (ts : alpha → OTerm beta) :
 (CellsBound count jobs branching cap).subst (fun a => emb (ts a)) =
 CellsBound (count.subst ts) (jobs.subst ts) (branching.subst ts) (cap.subst ts) := by
 unfold CellsBound cellMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [cellFieldsSubst,orderSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem cellsRename {beta : Type} (count jobs branching cap : OTerm alpha) (j : alpha → beta) :
 (CellsBound count jobs branching cap).relabel j =
 CellsBound (count.relabel j) (jobs.relabel j) (branching.relabel j) (cap.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (CellsBound count jobs branching cap).subst (fun a => emb (.var (j a))) = _
 rw [cellsSubst]
 simp only [← termRelabelAsSubst]
theorem cellWitness (count jobs branching cap index child value : OTerm alpha) :
 (cellMatrix count jobs branching cap).subst (Sum.elim Term.var (fun i => emb (![index,child,value] i))) =
 (cellFields count jobs branching index child value).imp (ltF value (suc cap)) := by
 have he : (Sum.elim Term.var (fun i => emb (![index,child,value] i))) =
   (fun a => emb (Sum.elim Term.var ![index,child,value] a)) := by funext a; cases a <;> rfl
 unfold cellMatrix
 rw [he,impSubst]
 simp only [cellFieldsSubst,orderSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem cellsApply (count jobs branching cap index child value : OTerm alpha)
 (h : Nonempty (Derivation body Delta (CellsBound count jobs branching cap)))
 (hf : Nonempty (Derivation body Delta (cellFields count jobs branching index child value))) :
 Nonempty (Derivation body Delta (ltF value (suc cap))) := by
 have hh := actualFiniteUniversalElimination body alpha 3 Delta (cellMatrix count jobs branching cap)
   (fun i => emb (![index,child,value] i)) h
 rw [cellWitness] at hh
 obtain ⟨hh⟩ := hh
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination hh hf⟩

def fields (depth b c v w : OTerm alpha) : Formula alpha :=
 lengthGraph depth b ⊓ (CellsBound depth b c v ⊓ graph2 OriginalHereditaryBudgetSum.sum w b c)
def result (depth v w : OTerm alpha) : Formula alpha := ltF w (suc (mul depth v))
def rowBody (depth : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields (depth.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (result (depth.relabel Sum.inl) (.var (.inr 2)) (.var (.inr 3)))
def row (depth : OTerm alpha) : Formula alpha := allBlock (rowBody depth)
theorem fieldsSubst {beta : Type} (depth b c v w : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields depth b c v w).subst (fun a => emb (ts a)) = fields (depth.subst ts) (b.subst ts) (c.subst ts) (v.subst ts) (w.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,cellsSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (depth b c v w : OTerm alpha) (j : alpha → beta) :
 (fields depth b c v w).relabel j = fields (depth.relabel j) (b.relabel j) (c.relabel j) (v.relabel j) (w.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,cellsRename,graph2Rename]
theorem resultSubst {beta : Type} (depth v w : OTerm alpha) (ts : alpha → OTerm beta) :
 (result depth v w).subst (fun a => emb (ts a)) = result (depth.subst ts) (v.subst ts) (w.subst ts) := by
 simp only [result,orderSubst,sucSubst,mulSubst]
@[simp] theorem resultRename {beta : Type} (depth v w : OTerm alpha) (j : alpha → beta) :
 (result depth v w).relabel j = result (depth.relabel j) (v.relabel j) (w.relabel j) := by
 simp only [result,orderRename,sucRelabel,mulRelabel]
theorem rowSubst {beta : Type} (depth : OTerm alpha) (ts : alpha → OTerm beta) :
 (row depth).subst (fun a => emb (ts a)) = row (depth.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (depth : OTerm alpha) (j : alpha → beta) :
 (row depth).relabel j = row (depth.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row depth).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowBodyWitness (depth b c v w : OTerm alpha) :
 (rowBody depth).subst (Sum.elim Term.var (fun i => emb (![b,c,v,w] i))) = (fields depth b c v w).imp (result depth v w) := by
 have he : (Sum.elim Term.var (fun i => emb (![b,c,v,w] i))) = (fun a => emb (Sum.elim Term.var ![b,c,v,w] a)) := by
  funext a
  cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (depth : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row depth) (emb t) = row (depth.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (depth : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row depth) = row (depth.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (depth b c v w : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row depth)))
 (hf : Nonempty (Derivation body Delta (fields depth b c v w))) :
 Nonempty (Derivation body Delta (result depth v w)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody depth) (fun i => emb (![b,c,v,w] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
