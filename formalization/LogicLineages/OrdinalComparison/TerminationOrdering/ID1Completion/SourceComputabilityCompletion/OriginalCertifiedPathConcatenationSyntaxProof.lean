module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationSyntaxProof
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
open OriginalCertifiedPathConcatenationDefinitions
variable {edge : Program 3}
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

@[simp] theorem resultRename {alpha beta : Type} (s t m : OTerm alpha) (j : alpha → beta) :
 (result edge s t m).relabel j = result edge (s.relabel j) (t.relabel j) (m.relabel j) := by
 simp only [result,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,
   programRename,consTermRename,emptyRename,sucRelabel,zRelabel]

theorem atRawSubst {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw edge raw).subst (fun a => emb (ts a)) = AtRaw edge (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw edge raw).relabel j = AtRaw edge (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw edge raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (input source middle target right combined : OTerm alpha) :
    (matrix edge input).subst (Sum.elim Term.var (fun i => emb (![source,middle,target,right,combined] i))) =
      (fields edge input source middle target right combined).imp (result edge source target combined) := by
  have he : (Sum.elim Term.var (fun i => emb (![source,middle,target,right,combined] i))) =
      (fun a => emb (Sum.elim Term.var ![source,middle,target,right,combined] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,equalSubst,result,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate edge) (emb raw) = AtRaw edge raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw edge raw).relabel j = BelowRaw edge (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type}  :
    lift (rawPredicate edge (alpha := alpha)) = rawPredicate edge (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationSyntaxProof
