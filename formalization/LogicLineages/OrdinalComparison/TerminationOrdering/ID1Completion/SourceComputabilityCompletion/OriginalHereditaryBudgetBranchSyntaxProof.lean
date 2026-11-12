module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchSyntaxProof
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

open OriginalHereditaryFuelProgram (budget)
def fields (depth b c v w : OTerm alpha) : Formula alpha :=
 ltF b (suc c) ⊓ (graph2 budget v depth b ⊓ graph2 budget w depth c)
def result (v w : OTerm alpha) : Formula alpha := ltF v (suc w)
def rowBody (depth : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields (depth.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (result (.var (.inr 2)) (.var (.inr 3)))
def row (depth : OTerm alpha) : Formula alpha := allBlock (rowBody depth)
theorem fieldsSubst {beta : Type} (depth b c v w : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields depth b c v w).subst (fun a => emb (ts a)) = fields (depth.subst ts) (b.subst ts) (c.subst ts) (v.subst ts) (w.subst ts) := by
 simp only [fields,conjunctionSubst,orderSubst,sucSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {beta : Type} (depth b c v w : OTerm alpha) (j : alpha → beta) :
 (fields depth b c v w).relabel j = fields (depth.relabel j) (b.relabel j) (c.relabel j) (v.relabel j) (w.relabel j) := by
 simp only [fields,conjunctionRename,orderRename,sucRelabel,graph2Rename]
theorem resultSubst {beta : Type} (v w : OTerm alpha) (ts : alpha → OTerm beta) :
 (result v w).subst (fun a => emb (ts a)) = result (v.subst ts) (w.subst ts) := by
 simp only [result,orderSubst,sucSubst]
@[simp] theorem resultRename {beta : Type} (v w : OTerm alpha) (j : alpha → beta) :
 (result v w).relabel j = result (v.relabel j) (w.relabel j) := by
 simp only [result,orderRename,sucRelabel]
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
 (rowBody depth).subst (Sum.elim Term.var (fun i => emb (![b,c,v,w] i))) = (fields depth b c v w).imp (result v w) := by
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
 Nonempty (Derivation body Delta (result v w)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody depth) (fun i => emb (![b,c,v,w] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchSyntaxProof
