module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SyntaxProof
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

open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnSubst eqnRelabel zSubst sucSubst)
open InternalStrongInduction InternalStrongInductionSyntaxProof
open SourceHeadsFilterAdequacy.InductionSyntaxProof (implicationRename)

theorem atRankSubst {beta : Type} (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRank n raw).subst (fun a => emb (ts a)) = AtRank n (raw.subst ts) := by
  unfold AtRank matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRankRename {beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRank n raw).relabel j = AtRank n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRank n raw).subst (fun a => emb (.var (j a))) = _
  rw [atRankSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (raw key param out : OTerm alpha) :
    (matrix n raw).subst (Sum.elim Term.var (fun i => emb ((![key,param,out] : Fin 3 → OTerm alpha) i))) =
      (graph2 rank raw key param ⊓ graph2 (extract n) out key param).imp (BooleanValue out) := by
  have he : (Sum.elim Term.var (fun i => emb ((![key,param,out] : Fin 3 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![key,param,out] : Fin 3 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,conjunctionSubst,BooleanValue,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,eqnSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate (n : Nat) (raw : OTerm alpha) : instantiate (predicate n : Formula (alpha ⊕ Fin 1)) (emb raw) = AtRank n raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atRankSubst]
  simp only [InternalTagArithmeticSyntaxProof.varBind]

theorem predicateLift (n : Nat) : lift (predicate n : Formula (alpha ⊕ Fin 1)) = predicate n := by
  unfold predicate lift
  rw [atRankRename]
  rfl

@[simp] theorem belowRankRename {beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRank n raw).relabel j = BelowRank n (raw.relabel j) := by
  unfold BelowRank
  rw [InternalStrongInductionSyntaxProof.belowRename]
  congr 1
  unfold predicate
  rw [atRankRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SyntaxProof
