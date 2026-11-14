module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionSyntaxProof
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
open InductionDefinitions.Induction
open PrimaryMonotonicity.InclusionProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

@[simp] theorem resultRename {alpha beta : Type} (initial out : OTerm alpha) (j : alpha → beta) :
 (result initial out).relabel j = result (initial.relabel j) (out.relabel j) := by
 simp only [result,includedRename]

theorem atCountSubst {alpha beta : Type} 
    (E : Program 3) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E raw).subst (fun a => emb (ts a)) = AtCount E (raw.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,includedSubst,graph3,graph4,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atCountRename {alpha beta : Type} 
    (E : Program 3) (raw : OTerm alpha) (j : alpha → beta) :
    (AtCount E raw).relabel j = AtCount E (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E raw).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (E : Program 3) (count pool initial first parameter out : OTerm alpha) :
    (matrix E count).subst (Sum.elim Term.var (fun i => emb (![pool,initial,first,parameter,out] i))) =
      (fields E count pool initial first parameter out).imp (result initial out) := by
  have he : (Sum.elim Term.var (fun i => emb (![pool,initial,first,parameter,out] i))) =
      (fun a => emb (Sum.elim Term.var ![pool,initial,first,parameter,out] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,result,includedSubst,graph3,graph4,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionSyntaxProof
