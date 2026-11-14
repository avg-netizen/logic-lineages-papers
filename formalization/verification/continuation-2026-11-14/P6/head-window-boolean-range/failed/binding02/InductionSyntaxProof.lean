module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InductionDefinitions
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnSubst eqnRelabel zSubst sucSubst)
open InternalStrongInduction InternalStrongInductionSyntaxProof
open SourceHeadsFilterAdequacy.InductionSyntaxProof (implicationRename)

theorem orRename (p q : Formula alpha) {beta : Type} (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

@[simp] theorem booleanRename {beta : Type} (out : OTerm alpha) (j : alpha → beta) :
    (BooleanValue out).relabel j = BooleanValue (out.relabel j) := by
  simp only [BooleanValue,orRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem atRawSubst {beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (raw needle out : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb ((![needle,out] : Fin 2 → OTerm alpha) i))) =
      (graph2 contains out raw needle).imp (BooleanValue out) := by
  have he : (Sum.elim Term.var (fun i => emb ((![needle,out] : Fin 2 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![needle,out] : Fin 2 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate (raw : OTerm alpha) : instantiate (predicate : Formula (alpha ⊕ Fin 1)) (emb raw) = AtRaw raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atRawSubst]
  simp only [varBind]

theorem predicateLift : lift (predicate : Formula (alpha ⊕ Fin 1)) = predicate := by
  unfold predicate lift
  rw [atRawRename]
  rfl

@[simp] theorem belowRawRename {beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  congr 1
  unfold predicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof
