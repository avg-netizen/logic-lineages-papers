module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst equalRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsObserverCongruence
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem cellFieldsSubst {beta : Type} (Q T : Program 2) (count input parameter other otherParameter index a b: OTerm alpha) (ts : alpha → OTerm beta) :
 (cellFields Q T count input parameter other otherParameter index a b).subst (fun a => emb (ts a)) = cellFields Q T (count.subst ts) (input.subst ts) (parameter.subst ts) (other.subst ts) (otherParameter.subst ts) (index.subst ts) (a.subst ts) (b.subst ts) := by
 simp only [cellFields,conjunctionSubst,Below,orderSubst,graph3,programSubst,consTermSubst,emptySubst]

theorem cellSubst {beta : Type} (Q T : Program 2) (count input parameter other otherParameter: OTerm alpha) (ts : alpha → OTerm beta) :
 (CellAgreement Q T count input parameter other otherParameter).subst (fun a => emb (ts a)) = CellAgreement Q T (count.subst ts) (input.subst ts) (parameter.subst ts) (other.subst ts) (otherParameter.subst ts) := by
 unfold CellAgreement cellBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [cellFieldsSubst,equalSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem cellRename {beta : Type} (Q T : Program 2) (count input parameter other otherParameter: OTerm alpha) (rho : alpha → beta) :
 (CellAgreement Q T count input parameter other otherParameter).relabel rho = CellAgreement Q T (count.relabel rho) (input.relabel rho) (parameter.relabel rho) (other.relabel rho) (otherParameter.relabel rho) := by
 rw [formulaRelabelAsSubst]
 change (CellAgreement Q T count input parameter other otherParameter).subst (fun a => emb (.var (rho a))) = _
 rw [cellSubst]
 simp only [← termRelabelAsSubst]

theorem cellWitness (Q T : Program 2) (count input parameter other otherParameter index a b : OTerm alpha) :
 (cellBody Q T count input parameter other otherParameter).subst
   (Sum.elim Term.var (fun i => emb (![index,a,b] i))) =
 (cellFields Q T count input parameter other otherParameter index a b).imp (equal a b) := by
 have he : (Sum.elim Term.var (fun i => emb (![index,a,b] i))) =
   (fun x => emb (Sum.elim Term.var ![index,a,b] x)) := by
   funext x
   cases x <;> rfl
 unfold cellBody
 rw [he,impSubst]
 simp only [cellFieldsSubst,equalSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl

theorem cellApply (Q T : Program 2) (count input parameter other otherParameter index a b : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (CellAgreement Q T count input parameter other otherParameter)))
 (hf : Nonempty (Derivation body Delta (cellFields Q T count input parameter other otherParameter index a b))) :
 Nonempty (Derivation body Delta (equal a b)) := by
 have h := actualFiniteUniversalElimination body alpha 3 Delta (cellBody Q T count input parameter other otherParameter)
   (fun i => emb (![index,a,b] i)) hc
 rw [cellWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩

def fields (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha) : Formula alpha :=
 CellAgreement Q T count input parameter other otherParameter ⊓
 (graph3 (scan Q) left count input parameter ⊓ graph3 (scan T) right count other otherParameter)
def rowBody (Q T : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields Q T (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (equal (.var (.inr 4)) (.var (.inr 5)))
def row (Q T : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (rowBody Q T count)

theorem fieldsSubst {beta : Type} (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields Q T count input parameter other otherParameter left right).subst (fun a => emb (ts a)) = fields Q T (count.subst ts) (input.subst ts) (parameter.subst ts) (other.subst ts) (otherParameter.subst ts) (left.subst ts) (right.subst ts) := by
 simp only [fields,conjunctionSubst,cellSubst,graph3,programSubst,consTermSubst,emptySubst]

theorem fieldsRename {beta : Type} (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha) (rho : alpha → beta) :
 (fields Q T count input parameter other otherParameter left right).relabel rho = fields Q T (count.relabel rho) (input.relabel rho) (parameter.relabel rho) (other.relabel rho) (otherParameter.relabel rho) (left.relabel rho) (right.relabel rho) := by
 rw [formulaRelabelAsSubst]
 change (fields Q T count input parameter other otherParameter left right).subst (fun a => emb (.var (rho a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]

theorem rowSubst {beta : Type} (Q T : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (row Q T count).subst (fun a => emb (ts a)) = row Q T (count.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,equalSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (Q T : Program 2) (count : OTerm alpha) (rho : alpha → beta) :
 (row Q T count).relabel rho = row Q T (count.relabel rho) := by
 rw [formulaRelabelAsSubst]
 change (row Q T count).subst (fun a => emb (.var (rho a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowWitness (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha) :
 (rowBody Q T count).subst (Sum.elim Term.var (fun i => emb (![input,parameter,other,otherParameter,left,right] i))) =
 (fields Q T count input parameter other otherParameter left right).imp (equal left right) := by
 have he : (Sum.elim Term.var (fun i => emb (![input,parameter,other,otherParameter,left,right] i))) =
   (fun x => emb (Sum.elim Term.var ![input,parameter,other,otherParameter,left,right] x)) := by
   funext x
   cases x <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,equalSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (Q T : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row Q T count) (emb t) = row Q T (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (Q T : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row Q T count) = row Q T (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row Q T count)))
 (hf : Nonempty (Derivation body Delta (fields Q T count input parameter other otherParameter left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody Q T count)
   (fun i => emb (![input,parameter,other,otherParameter,left,right] i)) hi
 rw [rowWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
