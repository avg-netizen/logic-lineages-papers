module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SortWeightedSortInductionDefinitions SortWeightedDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

variable {k : Nat} (F : Program (k+1))
theorem atRawSubst {alpha beta : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) (ts : alpha → OTerm beta) :
 (AtRaw F raw params).subst (fun a => emb (ts a)) =
 AtRaw F (raw.subst ts) (fun i => (params i).subst ts) := by
 unfold AtRaw matrix fields result
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,conjunctionSubst,graph1,programSubst,addSubst,
   consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (AtRaw F raw params).relabel j =
 AtRaw F (raw.relabel j) (fun i => (params i).relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtRaw F raw params).subst (fun a => emb (.var (j a))) = _
 rw [atRawSubst]
 simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw sorted sum : OTerm alpha)
 (params : Fin k → OTerm alpha) :
 (matrix F raw params).subst (Sum.elim Term.var (fun i => emb (![sorted,sum] i))) =
 (fields F raw sorted sum params).imp (result F sorted sum params) := by
 have he : (Sum.elim Term.var (fun i => emb (![sorted,sum] i))) =
   (fun a => emb (Sum.elim Term.var ![sorted,sum] a)) := by
   funext a; cases a <;> rfl
 unfold matrix fields result
 rw [he]
 simp only [impSubst,conjunctionSubst,graph1,programSubst,addSubst,
   consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl

theorem rawPredicateInstantiate {alpha : Type} (raw : OTerm alpha)
 (params : Fin k → OTerm alpha) :
 instantiate (rawPredicate F params) (emb raw) = AtRaw F raw params := by
 rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
 simp only [varBind,liftBind]

@[simp] theorem belowRawRename {alpha beta : Type}
 (raw : OTerm alpha) (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (BelowRaw F raw params).relabel j =
 BelowRaw F (raw.relabel j) (fun i => (params i).relabel j) := by
 unfold BelowRaw
 rw [InternalStrongInductionSyntaxProof.belowRename]
 unfold rawPredicate
 rw [atRawRename]
 simp only [Term.relabel_relabel, varMap, mapInl] <;> rfl

theorem rawPredicateLift {alpha : Type} (params : Fin k → OTerm alpha) :
 lift (rawPredicate F params) = rawPredicate F (fun i => (params i).relabel (Sum.inl : alpha → alpha ⊕ Fin 1)) := by
 unfold lift rawPredicate
 rw [atRawRename]
 simp only [Term.relabel_relabel, varMap, mapInl] <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionSyntax
