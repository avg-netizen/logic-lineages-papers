module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
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


open InternalOriginalOrderSyntaxProof
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open PrimaryUncoveredCount.OrderProof (boundedRename)
@[simp] theorem budgetRename {alpha beta : Type}
    (elapsed initialRemaining remaining out next : OTerm alpha) (j : alpha → beta) :
    (budget elapsed initialRemaining remaining out next).relabel j =
      budget (elapsed.relabel j) (initialRemaining.relabel j) (remaining.relabel j)
        (out.relabel j) (next.relabel j) := by
  simp only [budget,PrimaryExpansionSoundness.AppendSyntaxProof.orRename,includedRename,boundedRename,addRelabel]
theorem budgetSubst {alpha beta : Type}
    (elapsed initialRemaining remaining out next : OTerm alpha) (ts : alpha → OTerm beta) :
    (budget elapsed initialRemaining remaining out next).subst (fun a => emb (ts a)) =
      budget (elapsed.subst ts) (initialRemaining.subst ts) (remaining.subst ts)
        (out.subst ts) (next.subst ts) := by
  simp only [budget,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,includedSubst,boundedSubst,addSubst]
theorem fieldsSubst {alpha beta : Type} (E : Program 3)
    (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields E elapsed pool initial parameter out next initialRemaining remaining).subst (fun a => emb (ts a)) =
      fields E (elapsed.subst ts) (pool.subst ts) (initial.subst ts) (parameter.subst ts)
        (out.subst ts) (next.subst ts) (initialRemaining.subst ts) (remaining.subst ts) := by
  simp only [fields,conjunctionSubst,graph2,graph3,graph4,programSubst,consTermSubst,emptySubst]
theorem atCountSubst {alpha beta : Type} (E : Program 3) (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E elapsed).subst (fun a => emb (ts a)) = AtCount E (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSubst,budgetSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (E : Program 3) (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount E elapsed).relabel j = AtCount E (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type} (E : Program 3)
    (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha) :
    (matrix E elapsed).subst (Sum.elim Term.var
      (fun i => emb (![pool,initial,parameter,out,next,initialRemaining,remaining] i))) =
      (fields E elapsed pool initial parameter out next initialRemaining remaining).imp
        (budget elapsed initialRemaining remaining out next) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![pool,initial,parameter,out,next,initialRemaining,remaining] i))) =
      (fun a => emb (Sum.elim Term.var ![pool,initial,parameter,out,next,initialRemaining,remaining] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fieldsSubst,budgetSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionSyntaxProof
