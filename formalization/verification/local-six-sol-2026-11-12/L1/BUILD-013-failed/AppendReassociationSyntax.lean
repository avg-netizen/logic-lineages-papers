module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def fields (count a b c ab bc out : OTerm alpha) : Formula alpha :=
 lengthGraph count a ⊓ (graph2 InternalApplicationValidityStackAppend.append ab a b ⊓
 (graph2 InternalApplicationValidityStackAppend.append bc b c ⊓
  graph2 InternalApplicationValidityStackAppend.append out ab c))
def result (a bc out : OTerm alpha) : Formula alpha :=
 graph2 InternalApplicationValidityStackAppend.append out a bc
def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (result (.var (.inr 0)) (.var (.inr 4)) (.var (.inr 5)))
def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)
theorem fieldsSubst {beta : Type} (count a b c ab bc out : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields count a b c ab bc out).subst (fun x => emb (ts x)) =
 fields (count.subst ts) (a.subst ts) (b.subst ts) (c.subst ts) (ab.subst ts) (bc.subst ts) (out.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem fieldsRename {beta : Type} (count a b c ab bc out : OTerm alpha) (j : alpha → beta) :
 (fields count a b c ab bc out).relabel j =
 fields (count.relabel j) (a.relabel j) (b.relabel j) (c.relabel j) (ab.relabel j) (bc.relabel j) (out.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,graph2Rename]
theorem resultSubst {beta : Type} (a bc out : OTerm alpha) (ts : alpha → OTerm beta) :
 (result a bc out).subst (fun x => emb (ts x)) = result (a.subst ts) (bc.subst ts) (out.subst ts) := by
 simp only [result,graph2,programSubst,consTermSubst,emptySubst]
theorem resultRename {beta : Type} (a bc out : OTerm alpha) (j : alpha → beta) :
 (result a bc out).relabel j = result (a.relabel j) (bc.relabel j) (out.relabel j) := by
 simp only [result,graph2Rename]
theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (row count).subst (fun x => emb (ts x)) = row (count.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
 (row count).relabel j = row (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row count).subst (fun x => emb (.var (j x))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowBodyWitness (count a b c ab bc out : OTerm alpha) :
 (rowBody count).subst (Sum.elim Term.var (fun i => emb (![a,b,c,ab,bc,out] i))) =
 (fields count a b c ab bc out).imp (result a bc out) := by
 have he : (Sum.elim Term.var (fun i => emb (![a,b,c,ab,bc,out] i))) =
   (fun x => emb (Sum.elim Term.var ![a,b,c,ab,bc,out] x)) := by
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
theorem rowApply (count a b c ab bc out : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields count a b c ab bc out))) :
 Nonempty (Derivation body Delta (result a bc out)) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody count)
   (fun i => emb (![a,b,c,ab,bc,out] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationSyntax
