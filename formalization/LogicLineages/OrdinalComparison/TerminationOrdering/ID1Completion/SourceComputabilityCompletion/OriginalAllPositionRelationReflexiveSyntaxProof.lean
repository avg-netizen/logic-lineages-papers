module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveSyntaxProof
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
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def rowBody (R : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 graph4 (scan R) (suc z) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 0)) (.var (.inr 3))
def row (R : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (rowBody R count)

theorem rowSubst {beta : Type} (R : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (row R count).subst (fun a => emb (ts a)) = row R (count.subst ts) := by
 unfold row rowBody graph4
 rw [allBlockSubst,liftedEmbedding]
 simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst]

theorem rowRename {beta : Type} (R : Program 2) (count : OTerm alpha) (j : alpha → beta) :
 (row R count).relabel j = row R (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row R count).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]

theorem rowBodyWitness (R : Program 2) (count seed other candidate parameter : OTerm alpha) :
 (rowBody R count).subst (Sum.elim Term.var (fun i => emb (![seed,other,candidate,parameter] i))) =
 graph4 (scan R) (suc z) count seed seed parameter := by
 have he : (Sum.elim Term.var (fun i => emb (![seed,other,candidate,parameter] i))) =
   (fun a => emb (Sum.elim Term.var ![seed,other,candidate,parameter] a)) := by
   funext a
   cases a <;> rfl
 unfold rowBody graph4
 rw [he]
 simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,programSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst]
 rfl

theorem rowInstantiate (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row R count) (emb t) = row R (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row R count) = row R (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]

theorem rowApply (R : Program 2) (count seed parameter : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row R count))) :
 Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed seed parameter)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody R count)
   (fun i => emb (![seed,seed,seed,parameter] i)) hrow
 rw [rowBodyWitness] at h
 exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveSyntaxProof
