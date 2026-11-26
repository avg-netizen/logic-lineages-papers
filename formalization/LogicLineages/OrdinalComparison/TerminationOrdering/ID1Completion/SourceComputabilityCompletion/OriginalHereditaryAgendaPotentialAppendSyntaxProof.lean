module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
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

open InternalAdditionLawsProof (add addSubst)
open InternalOriginalOrderSyntaxProof (addRelabel)
def fields (count front suffix joined branching a b : OTerm alpha) : Formula alpha :=
 lengthGraph count front ⊓ (graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
 (graph2 OriginalHereditaryAgendaPotential.agenda a front branching ⊓ graph2 OriginalHereditaryAgendaPotential.agenda b suffix branching))
def result (joined branching a b : OTerm alpha) : Formula alpha :=
 graph2 OriginalHereditaryAgendaPotential.agenda (add a b) joined branching
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (result (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)
theorem fieldsSubst {beta : Type} (count front suffix joined branching a b : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields count front suffix joined branching a b).subst (fun a => emb (ts a)) = fields (count.subst ts) (front.subst ts) (suffix.subst ts) (joined.subst ts) (branching.subst ts) (a.subst ts) (b.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst,addSubst]
theorem fieldsRename {beta : Type} (count front suffix joined branching a b : OTerm alpha) (j : alpha → beta) :
 (fields count front suffix joined branching a b).relabel j = fields (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j) (branching.relabel j) (a.relabel j) (b.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,graph2Rename,addRelabel]
theorem resultSubst {beta : Type} (joined branching a b : OTerm alpha) (ts : alpha → OTerm beta) :
 (result joined branching a b).subst (fun a => emb (ts a)) = result (joined.subst ts) (branching.subst ts) (a.subst ts) (b.subst ts) := by
 simp only [result,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst,addSubst]
theorem resultRename {beta : Type} (joined branching a b : OTerm alpha) (j : alpha → beta) :
 (result joined branching a b).relabel j = result (joined.relabel j) (branching.relabel j) (a.relabel j) (b.relabel j) := by
 simp only [result,conjunctionRename,lengthRename,graph2Rename,addRelabel]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
 (row count).relabel j = row (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row count).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count front suffix joined branching a b : OTerm alpha) :
 (rowBody count).subst (Sum.elim Term.var (fun i => emb (![front,suffix,joined,branching,a,b] i))) = (fields count front suffix joined branching a b).imp (result joined branching a b) := by
 have he : (Sum.elim Term.var (fun i => emb (![front,suffix,joined,branching,a,b] i))) = (fun x => emb (Sum.elim Term.var ![front,suffix,joined,branching,a,b] x)) := by
  funext x
  cases x <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row count) = row (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (count front suffix joined branching a b : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields count front suffix joined branching a b))) :
 Nonempty (Derivation body Delta (result joined branching a b)) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody count) (fun i => emb (![front,suffix,joined,branching,a,b] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
