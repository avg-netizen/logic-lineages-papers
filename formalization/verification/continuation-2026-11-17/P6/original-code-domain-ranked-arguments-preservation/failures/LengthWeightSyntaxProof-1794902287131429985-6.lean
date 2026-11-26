module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LengthWeight
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementSyntaxProof
attribute [local irreducible] programGraph

theorem fieldsSubst {alpha beta : Type} (raw count out : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields raw count out).subst (fun a => emb (ts a)) =
      fields (raw.subst ts) (count.subst ts) (out.subst ts) := by
  simp only [fields,conjunctionSubst,graph2Subst,zSubst,graph1,programSubst,consTermSubst,emptySubst]
@[simp] theorem fieldsRename {alpha beta : Type} (raw count out : OTerm alpha) (j : alpha → beta) :
    (fields raw count out).relabel j = fields (raw.relabel j) (count.relabel j) (out.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields raw count out).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem resultSubst {alpha beta : Type} (raw out : OTerm alpha) (ts : alpha → OTerm beta) :
    (result raw out).subst (fun a => emb (ts a)) = result (raw.subst ts) (out.subst ts) := by
  simp only [result,graph1,programSubst,consTermSubst,emptySubst]
@[simp] theorem resultRename {alpha beta : Type} (raw out : OTerm alpha) (j : alpha → beta) :
    (result raw out).relabel j = result (raw.relabel j) (out.relabel j) := by
  simp only [result,InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw count out : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb (![count,out] i))) =
      (fields raw count out).imp (result raw out) := by
  have he : (Sum.elim Term.var (fun i => emb (![count,out] i))) =
      (fun a => emb (Sum.elim Term.var ![count,out] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem predicateInstantiate {alpha : Type} (raw : OTerm alpha) :
    instantiate (predicate) (emb raw) = AtRaw raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl

theorem predicateLift {alpha : Type} :
    lift (predicate (alpha := alpha)) = predicate (alpha := alpha ⊕ Fin 1) := by
  unfold lift predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightSyntaxProof
