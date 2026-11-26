module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersSyntaxProof
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
open OriginalRawSyntaxTransportInternalParameters
open InternalStrongInduction

theorem atRawSubst {alpha beta : Type} (p : Program 3) (rank : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw p rank raw).subst (fun a => emb (ts a)) = AtRaw p rank (raw.subst ts) := by
  unfold AtRaw parameterMatrix
  rw [allBlockSubst,liftedEmbedding]
  cases rank <;> simp only [Bool.false_eq_true,if_false,if_true,impSubst,graph3,programSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (p : Program 3) (rank : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw p rank raw).relabel j = AtRaw p rank (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw p rank raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem parameterMatrixWitness {alpha : Type} (p : Program 3) (rank : Bool)
    (raw out d k other otherK : OTerm alpha) :
    (parameterMatrix p rank raw).subst
      (Sum.elim Term.var (fun i => emb (![out,d,k,other,otherK] i))) =
      (graph3 p out d k raw).imp (graph3 p out other (if rank then otherK else k) raw) := by
  have he : (Sum.elim Term.var (fun i => emb (![out,d,k,other,otherK] i))) =
      (fun a => emb (Sum.elim Term.var ![out,d,k,other,otherK] a)) := by
    funext a
    cases a <;> rfl
  unfold parameterMatrix
  rw [he]
  cases rank <;> simp only [Bool.false_eq_true,if_false,if_true,impSubst,graph3,programSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem rawPredicateInstantiate {alpha : Type} (p : Program 3) (rank : Bool) (raw : OTerm alpha) :
    instantiate (rawPredicate p rank) (emb raw) = AtRaw p rank raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (p : Program 3) (rank : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw p rank raw).relabel j = BelowRaw p rank (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (p : Program 3) (rank : Bool) :
    lift (rawPredicate p rank (alpha := alpha)) = rawPredicate p rank (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersSyntaxProof
