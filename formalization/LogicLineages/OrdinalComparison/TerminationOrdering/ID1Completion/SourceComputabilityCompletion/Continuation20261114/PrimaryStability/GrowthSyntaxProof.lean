module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalOriginalOrderSyntaxProof
@[simp] theorem witnessSubst {alpha beta : Type}
    (pool before after : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (growthWitness pool before after).subst (fun a => emb (ts a)) =
      growthWitness (pool.subst ts) (before.subst ts) (after.subst ts) := by
  unfold growthWitness
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,notSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem witnessRename {alpha beta : Type}
    (pool before after : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (growthWitness pool before after).relabel j =
      growthWitness (pool.relabel j) (before.relabel j) (after.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (growthWitness pool before after).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]
theorem witnessInstance {alpha : Type}
    (pool before after candidate : OrdinaryArithmetic.Term alpha) :
    instantiate (graph2 contains (numeral 1) (pool.relabel Sum.inl) (.var (.inr 0)) ⊓
      ((graph2 contains (numeral 1) (before.relabel Sum.inl) (.var (.inr 0))).not ⊓
       graph2 contains (numeral 1) (after.relabel Sum.inl) (.var (.inr 0)))) (emb candidate) =
      (graph2 contains (numeral 1) pool candidate ⊓
        ((graph2 contains (numeral 1) before candidate).not ⊓ graph2 contains (numeral 1) after candidate)) := by
  rw [instantiate,bindEmbedding]
  simp only [conjunctionSubst,notSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthSyntaxProof
