module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionSyntaxProof
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
open Continuation20261114
open InductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open PrimaryUncoveredCount.OrderProof (boundedRename)
@[simp] theorem resultRename {alpha beta : Type} (depth seed child : OTerm alpha) (j : alpha → beta) :
    (result depth seed child).relabel j = result (depth.relabel j) (seed.relabel j) (child.relabel j) := by
  simp only [result,boundedRename,addRelabel]
theorem resultSubst {alpha beta : Type} (depth seed child : OTerm alpha) (ts : alpha → OTerm beta) :
    (result depth seed child).subst (fun a => emb (ts a)) = result (depth.subst ts) (seed.subst ts) (child.subst ts) := by
  simp only [result,boundedSubst,addSubst]
theorem atCountSubst {alpha beta : Type} 
    (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount n raw).subst (fun a => emb (ts a)) = AtCount n (raw.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,resultSubst]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atCountRename {alpha beta : Type} 
    (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (AtCount n raw).relabel j = AtCount n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount n raw).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (depth seed param frontier child seedRank childRank : OTerm alpha) :
    (matrix n depth).subst (Sum.elim Term.var (fun i => emb (![seed,param,frontier,child,seedRank,childRank] i))) =
      (fields n depth seed param frontier child seedRank childRank).imp (result depth seedRank childRank) := by
  have he : (Sum.elim Term.var (fun i => emb (![seed,param,frontier,child,seedRank,childRank] i))) =
      (fun a => emb (Sum.elim Term.var ![seed,param,frontier,child,seedRank,childRank] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,resultSubst]
  simp only [impSubst,conjunctionSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.InductionSyntaxProof
