module
import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareSyntaxProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus (Formula Term instantiate)
open ID1Completion.InternalControlGraph
open InternalApplicationCertificateConstructors
open ID1Completion.InternalControlGraphSupportProof (programRename emptyRename)
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalScratchInclusionThinProof (included includedRename includedSubst)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalThinUncoveredCountCompareDefinitions.Compare
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalStrongInduction

private theorem orSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

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
  simp only [result,newness,NumberedWindowInternalThinUncoveredCountOrderProof.boundedRename,conjunctionRename,implicationRename,negationRename,orderRename,eqnRelabel,
    graph2,programRename,consTermRename,emptyRename,sucRelabel,zRelabel]


theorem boundedSubst {alpha beta : Type} (a b : OTerm alpha) (ts : alpha → OTerm beta) :
    (bounded a b).subst (fun x => emb (ts x)) = bounded (a.subst ts) (b.subst ts) := by
  unfold bounded
  rw [orSubst _ _ (fun x => emb (ts x)), orderSubst, eqnSubst]

theorem newnessSubst {alpha beta : Type} (raw left right candidate : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (newness raw left right candidate).subst (fun x => emb (ts x)) =
      newness (raw.subst ts) (left.subst ts) (right.subst ts) (candidate.subst ts) := by
  simp only [newness,conjunctionSubst,InternalOriginalOrderSyntaxProof.notSubst,
    graph2,programSubst,consTermSubst,emptySubst,sucSubst,zSubst]

theorem fieldsSubst {alpha beta : Type} (raw left right a b candidate : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fields raw left right a b candidate).subst (fun x => emb (ts x)) =
      fields (raw.subst ts) (left.subst ts) (right.subst ts) (a.subst ts) (b.subst ts) (candidate.subst ts) := by
  simp only [fields,conjunctionSubst,includedSubst,graph2,programSubst,consTermSubst,emptySubst]

theorem resultSubst {alpha beta : Type} (raw left right a b candidate : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (result raw left right a b candidate).subst (fun x => emb (ts x)) =
      result (raw.subst ts) (left.subst ts) (right.subst ts) (a.subst ts) (b.subst ts) (candidate.subst ts) := by
  simp only [result,conjunctionSubst,impSubst,boundedSubst,newnessSubst,orderSubst]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSubst,resultSubst,liftSubst,FirstOrder.Language.Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (raw left right leftCount rightCount candidate : OTerm alpha) :
    (matrix raw).subst (Sum.elim FirstOrder.Language.Term.var (fun i => emb (![left,right,leftCount,rightCount,candidate] i))) =
      (fields raw left right leftCount rightCount candidate).imp (result raw left right leftCount rightCount candidate) := by
  have he : (Sum.elim FirstOrder.Language.Term.var (fun i => emb (![left,right,leftCount,rightCount,candidate] i))) =
      (fun a => emb (Sum.elim FirstOrder.Language.Term.var ![left,right,leftCount,rightCount,candidate] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fieldsSubst,resultSubst,witnessLift,FirstOrder.Language.Term.subst,Sum.elim_inr]
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

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareSyntaxProof
