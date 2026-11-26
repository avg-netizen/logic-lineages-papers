module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
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
open CompareDefinitions.Compare
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open InternalStrongInduction
open PrimaryMonotonicity.InclusionProof

theorem orRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl


theorem implicationRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl
theorem negationRename {alpha beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

@[simp] theorem resultRename {alpha beta : Type}
    (raw left right leftCount rightCount candidate : OTerm alpha) (j : alpha → beta) :
    (result raw left right leftCount rightCount candidate).relabel j =
      result (raw.relabel j) (left.relabel j) (right.relabel j) (leftCount.relabel j)
        (rightCount.relabel j) (candidate.relabel j) := by
  simp only [result,newness,bounded,conjunctionRename,implicationRename,negationRename,orRename,orderRename,eqnRelabel,
    graph2,programRename,consTermRename,emptyRename,sucRelabel,zRelabel]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fields,conjunctionSubst,result,newness,includedSubst,bounded,orSubst,orderSubst,eqnSubst,
    graph2,OriginalContextInsertion.lengthGraph,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (raw left right leftCount rightCount candidate : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb (![left,right,leftCount,rightCount,candidate] i))) =
      (fields raw left right leftCount rightCount candidate).imp (result raw left right leftCount rightCount candidate) := by
  have he : (Sum.elim Term.var (fun i => emb (![left,right,leftCount,rightCount,candidate] i))) =
      (fun a => emb (Sum.elim Term.var ![left,right,leftCount,rightCount,candidate] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fields,conjunctionSubst,result,newness,includedSubst,bounded,orSubst,orderSubst,eqnSubst,
    graph2,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate) (emb raw) = AtRaw raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type}  :
    lift (rawPredicate (alpha := alpha)) = rawPredicate (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
