module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceInductionSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb suc)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax
open SixSol20261113.Erasure.EvaluatorErasureDefinitions SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (bindTerm bindEmbedding nextTerm nextEmbedding)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def rowBody (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (AllSteps (trace.relabel Sum.inl) (steps.relabel Sum.inl) (c.relabel Sum.inl) ⊓
 StateAt (trace.relabel Sum.inl) (steps.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (AdmittedPair R H G M W (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))
def row (R : Program 2) (H G : Program 1) (M W : Program 2) (trace steps c : OTerm alpha) : Formula alpha :=
 allBlock (rowBody R H G M W trace steps c)
theorem rowSubst {beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm alpha) (ts : alpha → OTerm beta) :
 (row R H G M W trace steps c).subst (fun a => emb (ts a)) =
 row R H G M W (trace.subst ts) (steps.subst ts) (c.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [conjunctionSubst,allSubst,stateSubst,admittedSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm alpha) (j : alpha → beta) :
 (row R H G M W trace steps c).relabel j = row R H G M W (trace.relabel j) (steps.relabel j) (c.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row R H G M W trace steps c).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowWitness (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c left right parameter gamma : OTerm alpha) :
 (rowBody R H G M W trace steps c).subst (Sum.elim Term.var (fun i => emb (![left,right,parameter,gamma] i))) =
 (AllSteps trace steps c ⊓ StateAt trace steps left right parameter gamma).imp (AdmittedPair R H G M W left right parameter) := by
 have he : (Sum.elim Term.var (fun i => emb (![left,right,parameter,gamma] i))) =
   (fun a => emb (Sum.elim Term.var ![left,right,parameter,gamma] a)) := by funext a; cases a <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [conjunctionSubst,allSubst,stateSubst,admittedSubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
theorem rowApply (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c left right parameter gamma : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row R H G M W trace steps c)))
 (ha : Nonempty (Derivation body Delta (AllSteps trace steps c)))
 (hs : Nonempty (Derivation body Delta (StateAt trace steps left right parameter gamma))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody R H G M W trace steps c)
   (fun i => emb (![left,right,parameter,gamma] i)) hr
 rw [rowWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := InternalApplicationStepPeelSupportProof.andIntro ha hs
 exact ⟨Derivation.implicationElimination h hf⟩
theorem rowInstantiate (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row R H G M W trace steps c) (emb t) =
 row R H G M W (trace.subst (bindTerm t)) (steps.subst (bindTerm t)) (c.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (R : Program 2) (H G : Program 1) (M W : Program 2)
 (trace steps c : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row R H G M W trace steps c) =
 row R H G M W (trace.subst nextTerm) (steps.subst nextTerm) (c.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceInductionSyntax
