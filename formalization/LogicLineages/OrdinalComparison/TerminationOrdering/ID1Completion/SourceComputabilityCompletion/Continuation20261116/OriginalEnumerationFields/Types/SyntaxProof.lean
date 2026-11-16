module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.SyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zSubst sucSubst)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalStrongInduction InternalStrongInductionSyntaxProof
open Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem resultSubst {beta : Type} (raw allowed : OTerm alpha) (ts : alpha → OTerm beta) :
    (result raw allowed).subst (fun a => emb (ts a)) = result (raw.subst ts) (allowed.subst ts) := by
  unfold result
  simp only [conjunctionSubst,impSubst,membersSubst,graph2,programSubst,zSubst,sucSubst,consTermSubst,emptySubst]

theorem resultRename {beta : Type} (raw allowed : OTerm alpha) (j : alpha → beta) :
    (result raw allowed).relabel j = result (raw.relabel j) (allowed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result raw allowed).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding,resultSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem atRawRename {beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (raw allowed : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun _ : Fin 1 => emb allowed)) = result raw allowed := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb allowed)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => allowed) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,resultSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem predicateInstantiate (raw : OTerm alpha) : instantiate (predicate : Formula (alpha ⊕ Fin 1)) (emb raw) = AtRaw raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atRawSubst]
  simp only [InternalTagArithmeticSyntaxProof.varBind]

theorem predicateLift : lift (predicate : Formula (alpha ⊕ Fin 1)) = predicate := by
  unfold predicate lift
  rw [atRawRename]
  rfl

theorem belowRawRename {beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  congr 1
  unfold predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.SyntaxProof
