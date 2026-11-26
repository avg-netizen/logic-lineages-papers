module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb liftBind varBind bindEmbedding)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)
open InternalComputabilityApplicationSyntaxProof (programSubst)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (argumentsAcceptedSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentInductionDefinitions RankArgumentSyntax
open InternalStrongInduction
variable {alpha : Type} {k : Nat}
variable (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
theorem atRawSubst {beta : Type} (parameter gamma c bound raw : OTerm alpha)
 (params : Fin k → OTerm alpha) (ts : alpha → OTerm beta) :
 (AtRaw Q F H M W parameter gamma c bound raw params).subst (fun a => emb (ts a)) =
 AtRaw Q F H M W (parameter.subst ts) (gamma.subst ts) (c.subst ts) (bound.subst ts)
   (raw.subst ts) (fun i => (params i).subst ts) := by
 unfold AtRaw matrix fields
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,conjunctionSubst,argumentsAcceptedSubst,smallSubst,
   graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem atRawRename {beta : Type} (parameter gamma c bound raw : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (AtRaw Q F H M W parameter gamma c bound raw params).relabel j =
 AtRaw Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j) (bound.relabel j)
   (raw.relabel j) (fun i => (params i).relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtRaw Q F H M W parameter gamma c bound raw params).subst (fun a => emb (.var (j a))) = _
 rw [atRawSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness (parameter gamma c bound raw types observations rank : OTerm alpha)
 (params : Fin k → OTerm alpha) :
 (matrix Q F H M W parameter gamma c bound raw params).subst
   (Sum.elim Term.var (fun i => emb (![types,observations,rank] i))) =
 (fields Q H M W parameter gamma c bound raw types observations rank).imp
 (programGraph (SortWeightedDefinitions.weighted F) rank (Fin.cons observations params)) := by
 have he : (Sum.elim Term.var (fun i => emb (![types,observations,rank] i))) =
   (fun a => emb (Sum.elim Term.var ![types,observations,rank] a)) := by funext a; cases a <;> rfl
 unfold matrix fields
 rw [he]
 simp only [impSubst,conjunctionSubst,argumentsAcceptedSubst,smallSubst,
   graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rawPredicateInstantiate (parameter gamma c bound raw : OTerm alpha)
 (params : Fin k → OTerm alpha) :
 instantiate (rawPredicate Q F H M W parameter gamma c bound params) (emb raw) =
 AtRaw Q F H M W parameter gamma c bound raw params := by
 rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
 simp only [varBind,liftBind]
theorem belowRawRename {beta : Type} (parameter gamma c bound raw : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (BelowRaw Q F H M W parameter gamma c bound raw params).relabel j =
 BelowRaw Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j) (bound.relabel j)
   (raw.relabel j) (fun i => (params i).relabel j) := by
 unfold BelowRaw
 rw [InternalStrongInductionSyntaxProof.belowRename]
 unfold rawPredicate
 rw [atRawRename]
 simp only [Term.relabel_relabel]
 rfl
theorem rawPredicateLift (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha) :
 lift (rawPredicate Q F H M W parameter gamma c bound params) =
 rawPredicate Q F H M W (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
   (c.relabel Sum.inl) (bound.relabel Sum.inl) (fun i => (params i).relabel Sum.inl) := by
 unfold lift rawPredicate
 rw [atRawRename]
 simp only [Term.relabel_relabel]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionSyntax
