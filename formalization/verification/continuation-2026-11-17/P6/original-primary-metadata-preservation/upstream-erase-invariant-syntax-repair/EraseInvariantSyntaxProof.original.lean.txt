module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantSyntaxProof
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
open EraseInvariant
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

theorem countEffectSubst {alpha beta : Type} (raw needle rest bit : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (countEffect raw needle rest bit).subst (fun a => emb (ts a)) =
      countEffect (raw.subst ts) (needle.subst ts) (rest.subst ts) (bit.subst ts) := by
  unfold countEffect
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,notSubst,eqnSubst,graph2,programSubst,
    consTermSubst,emptySubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem countEffectRename {alpha beta : Type} (raw needle rest bit : OTerm alpha)
    (j : alpha → beta) :
    (countEffect raw needle rest bit).relabel j =
      countEffect (raw.relabel j) (needle.relabel j) (rest.relabel j) (bit.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (countEffect raw needle rest bit).subst (fun a => emb (.var (j a))) = _
  rw [countEffectSubst]
  simp only [← termRelabelAsSubst]

theorem countEffectWitness {alpha : Type} (raw needle rest bit query lc rc : OTerm alpha) :
    ((let j : alpha → alpha ⊕ Fin 3 := Sum.inl
      let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
      (graph2 ArgumentEntryCount.count (x 1) (raw.relabel j) (x 0) ⊓
       graph2 ArgumentEntryCount.count (x 2) (rest.relabel j) (x 0)).imp
       (((eqn (needle.relabel j) (x 0)).imp
          (eqn (x 1) (OrdinaryArithmetic.addTerm (x 2) (bit.relabel j)))) ⊓
        ((eqn (needle.relabel j) (x 0)).not.imp (eqn (x 1) (x 2))))) : Formula (alpha ⊕ Fin 3)).subst
      (Sum.elim Term.var (fun i => emb (![query,lc,rc] i))) =
    (graph2 ArgumentEntryCount.count lc raw query ⊓ graph2 ArgumentEntryCount.count rc rest query).imp
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc bit))) ⊓
        ((eqn needle query).not.imp (eqn lc rc))) := by
  have he : (Sum.elim Term.var (fun i => emb (![query,lc,rc] i))) =
      (fun a => emb (Sum.elim Term.var ![query,lc,rc] a)) := by
    funext a; cases a <;> rfl
  rw [he]
  simp only [impSubst,conjunctionSubst,notSubst,eqnSubst,graph2,programSubst,
    consTermSubst,emptySubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,fields,result,orSubst,countEffectSubst,eqnSubst,
    graph2,programSubst,zSubst,sucSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw needle acc bit rest : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (fields raw needle acc bit rest).imp (result raw needle bit rest) := by
  have he : (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (fun a => emb (Sum.elim Term.var ![needle,acc,bit,rest] a)) := by
    funext a; cases a <;> rfl
  unfold matrix fields result
  rw [he]
  simp only [impSubst,conjunctionSubst,orSubst,countEffectSubst,eqnSubst,graph2,programSubst,
    zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantSyntaxProof
