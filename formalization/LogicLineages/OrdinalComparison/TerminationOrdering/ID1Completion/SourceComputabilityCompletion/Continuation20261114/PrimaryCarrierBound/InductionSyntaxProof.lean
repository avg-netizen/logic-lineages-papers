module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
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
open Induction
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

@[simp] theorem resultRename {alpha beta : Type} (reached pool needle : OTerm alpha) (j : alpha → beta) :
 (result reached pool needle).relabel j = result (reached.relabel j) (pool.relabel j) (needle.relabel j) := by
 simp only [result,inCarrier,PrimaryExpansionSoundness.AppendSyntaxProof.orRename,graph2,programRename,
   consTermRename,emptyRename,numeral,sucRelabel,zRelabel]

theorem atCountSubst {alpha beta : Type} 
    (E : Program 3) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E raw).subst (fun a => emb (ts a)) = AtCount E (raw.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,inCarrier,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,graph2,graph4,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atCountRename {alpha beta : Type} 
    (E : Program 3) (raw : OTerm alpha) (j : alpha → beta) :
    (AtCount E raw).relabel j = AtCount E (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E raw).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (E : Program 3) (count pool reached parameter out needle : OTerm alpha) :
    (matrix E count).subst (Sum.elim Term.var (fun i => emb (![pool,reached,parameter,out,needle] i))) =
      (fields E count pool reached parameter out needle).imp (result reached pool needle) := by
  have he : (Sum.elim Term.var (fun i => emb (![pool,reached,parameter,out,needle] i))) =
      (fun a => emb (Sum.elim Term.var ![pool,reached,parameter,out,needle] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,result,inCarrier,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,graph2,graph4,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
