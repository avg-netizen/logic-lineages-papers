module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InductionDefinitions InclusionProof
@[simp] theorem atCountSubst {alpha beta : Type} (E : Program 3)
    (count : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (AtCount E count).subst (fun a => emb (ts a)) = AtCount E (count.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fields,conjunctionSubst,includedSubst,graph4,programSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (E : Program 3)
    (count : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (AtCount E count).relabel j = AtCount E (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E count).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type} (E : Program 3)
    (count pool left right parameter leftOut rightOut : OrdinaryArithmetic.Term alpha) :
    (matrix E count).subst (Sum.elim Term.var
      (fun i => emb (![pool,left,right,parameter,leftOut,rightOut] i))) =
      (fields E count pool left right parameter leftOut rightOut).imp (included leftOut rightOut) := by
  have he : (Sum.elim Term.var (fun i => emb (![pool,left,right,parameter,leftOut,rightOut] i))) =
      (fun a => emb (Sum.elim Term.var ![pool,left,right,parameter,leftOut,rightOut] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,fields,conjunctionSubst,includedSubst,graph4,programSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionSyntaxProof
