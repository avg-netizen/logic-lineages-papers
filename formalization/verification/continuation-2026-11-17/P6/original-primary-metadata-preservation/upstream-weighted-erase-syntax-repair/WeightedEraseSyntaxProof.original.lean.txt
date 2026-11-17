module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
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
open WeightedErase
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

theorem effectSubst {alpha beta : Type} (bit total remainingWeight needleWeight : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (effect bit total remainingWeight needleWeight).subst (fun a => emb (ts a)) =
    effect (bit.subst ts) (total.subst ts) (remainingWeight.subst ts) (needleWeight.subst ts) := by
  unfold effect
  simp only [conjunctionSubst,impSubst,eqnSubst,graph2,programSubst,
    consTermSubst,emptySubst,zSubst,sucSubst]

@[simp] theorem effectRename {alpha beta : Type} (bit total remainingWeight needleWeight : OTerm alpha)
    (j : alpha → beta) :
    (effect bit total remainingWeight needleWeight).relabel j =
    effect (bit.relabel j) (total.relabel j) (remainingWeight.relabel j) (needleWeight.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (effect bit total remainingWeight needleWeight).subst (fun a => emb (.var (j a))) = _
  rw [effectSubst]
  simp only [← termRelabelAsSubst]

theorem fieldsSubst {alpha beta : Type} (weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fields weight raw needle acc bit rest total remainingWeight needleWeight).subst (fun a => emb (ts a)) =
    fields weight (raw.subst ts) (needle.subst ts) (acc.subst ts) (bit.subst ts) (rest.subst ts)
      (total.subst ts) (remainingWeight.subst ts) (needleWeight.subst ts) := by
  unfold fields EraseInvariant.fields
  simp only [conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem fieldsRename {alpha beta : Type} (weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha) (j : alpha → beta) :
    (fields weight raw needle acc bit rest total remainingWeight needleWeight).relabel j =
    fields weight (raw.relabel j) (needle.relabel j) (acc.relabel j) (bit.relabel j) (rest.relabel j)
      (total.relabel j) (remainingWeight.relabel j) (needleWeight.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields weight raw needle acc bit rest total remainingWeight needleWeight).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (weight : Program 1) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw weight raw).subst (fun a => emb (ts a)) = AtRaw weight (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSubst,effectSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (weight : Program 1) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw weight raw).relabel j = AtRaw weight (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw weight raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha) :
    (matrix weight raw).subst
      (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest,total,remainingWeight,needleWeight] i))) =
    (fields weight raw needle acc bit rest total remainingWeight needleWeight).imp
      (effect bit total remainingWeight needleWeight) := by
  have he : (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest,total,remainingWeight,needleWeight] i))) =
      (fun a => emb (Sum.elim Term.var ![needle,acc,bit,rest,total,remainingWeight,needleWeight] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fieldsSubst,effectSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate {alpha : Type} (weight : Program 1) (raw : OTerm alpha) :
    instantiate (predicate weight) (emb raw) = AtRaw weight raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (weight : Program 1) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw weight raw).relabel j = BelowRaw weight (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl

theorem predicateLift {alpha : Type} (weight : Program 1) :
    lift (predicate (alpha := alpha) weight) = predicate (alpha := alpha ⊕ Fin 1) weight := by
  unfold lift predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
