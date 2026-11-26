module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSchemaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceGenericSyntaxProof
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
open EraseAbsenceSchema
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

variable (C S : Program 2)
attribute [local irreducible] programGraph

theorem resultSubst {alpha beta : Type} (raw needle bit : OTerm alpha) (ts : alpha → OTerm beta) :
    (result C raw needle bit).subst (fun a => emb (ts a)) = result C (raw.subst ts) (needle.subst ts) (bit.subst ts) := by
  simp only [result,impSubst,eqnSubst,zSubst,graph2,programSubst,consTermSubst,emptySubst]
@[simp] theorem resultRename {alpha beta : Type} (raw needle bit : OTerm alpha) (j : alpha → beta) :
    (result C raw needle bit).relabel j = result C (raw.relabel j) (needle.relabel j) (bit.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result C raw needle bit).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst C]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw C S raw).subst (fun a => emb (ts a)) = AtRaw C S (raw.subst ts) := by
  unfold AtRaw matrix fields
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,resultSubst C,graph2,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw C S raw).relabel j = AtRaw C S (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw C S raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst C S]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw needle acc bit rest : OTerm alpha) :
    (matrix C S raw).subst (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (fields S raw needle acc bit rest).imp (result C raw needle bit) := by
  have he : (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (fun a => emb (Sum.elim Term.var ![needle,acc,bit,rest] a)) := by
    funext a; cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,resultSubst C,graph2,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
  rfl
theorem predicateInstantiate {alpha : Type} (raw : OTerm alpha) :
    instantiate (predicate C S) (emb raw) = AtRaw C S raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst C S]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw C S raw).relabel j = BelowRaw C S (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename C S]
  rfl

theorem predicateLift {alpha : Type} :
    lift (predicate C S (alpha := alpha)) = predicate C S (alpha := alpha ⊕ Fin 1) := by
  unfold lift predicate
  rw [atRawRename C S]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceGenericSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceGenericSyntaxProof
