module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderRowDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderSyntaxProof
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
open OriginalTypedArgumentPrefixBuilderRowDefinitions OriginalTypedArgumentObservations
variable (R : Program 2)
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

theorem atRawSubst {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw R raw).subst (fun a => emb (ts a)) = AtRaw R (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,graph1,graph2,programSubst,numeral,zSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw R raw).relabel j = AtRaw R (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw R raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (input suffix built parameter mappedValue suffixValue total : OTerm alpha) :
    (matrix R input).subst (Sum.elim Term.var (fun i => emb (![suffix,built,parameter,mappedValue,suffixValue,total] i))) =
      (fields R input suffix built parameter mappedValue suffixValue total).imp (graph2 (argumentObservations R) total built parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![suffix,built,parameter,mappedValue,suffixValue,total] i))) =
      (fun a => emb (Sum.elim Term.var ![suffix,built,parameter,mappedValue,suffixValue,total] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,equalSubst,graph1,graph2,programSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate R) (emb raw) = AtRaw R raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw R raw).relabel j = BelowRaw R (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type}  :
    lift (rawPredicate (alpha := alpha) R) = rawPredicate (alpha := alpha ⊕ Fin 1) R := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderSyntaxProof
